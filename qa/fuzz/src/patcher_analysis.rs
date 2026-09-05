//! Post-synthesis graph and bounded rank analysis for recorded circuits.
//!
//! [`analyze_connectivity`] treats wires as vertices and each recorded
//! constraint or definition as a hyperedge. [`analyze_component_rank`] then
//! runs the exact Jacobian rank/nullity oracle independently on components
//! small enough for dense elimination. These checks inspect a synthesized
//! graph without mutating or re-running its witness.

use std::collections::BTreeMap;

use ragu_arithmetic::ff::Field;
use ragu_testing::patcher::{Event, underconstrained_derived};

/// One connected subgraph of non-constant wires.
///
/// The fixed ONE wire is deliberately not used as a bridge: two otherwise
/// independent expressions that both mention a constant remain two
/// components. [`touches_one`](Self::touches_one) records that each component
/// is nevertheless anchored to the fixed constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConnectedSubgraph {
    /// Wires in the component, ascending.
    pub wires: Vec<usize>,
    /// Recorded event indices belonging to the component, ascending.
    pub events: Vec<usize>,
    /// Declared input wires in the component, ascending.
    pub inputs: Vec<usize>,
    /// Declared output wires in the component, ascending.
    pub outputs: Vec<usize>,
    /// Whether an event in the component also references the fixed ONE wire.
    pub touches_one: bool,
}

impl ConnectedSubgraph {
    /// Returns `true` for a wire or group of wires that no event references.
    pub fn is_isolated(&self) -> bool {
        self.events.is_empty()
    }

    /// Returns `true` for a component connected to neither a declared circuit
    /// boundary nor the fixed ONE wire.
    pub fn is_floating(&self) -> bool {
        self.inputs.is_empty() && self.outputs.is_empty() && !self.touches_one
    }
}

/// Connectivity census for a synthesized constraint graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConnectivityReport {
    /// Number of wires in the analyzed graph, including fixed ONE.
    pub wire_count: usize,
    /// Connected components excluding the fixed ONE wire, ordered by their
    /// smallest wire id.
    pub components: Vec<ConnectedSubgraph>,
    /// Events that mention no wire other than ONE.
    pub constant_only_events: Vec<usize>,
}

impl ConnectivityReport {
    /// Returns every wire that appears in no recorded event.
    pub fn isolated_wires(&self) -> Vec<usize> {
        self.components
            .iter()
            .filter(|component| component.is_isolated())
            .flat_map(|component| component.wires.iter().copied())
            .collect()
    }

    /// Returns indices into [`components`](Self::components) for subgraphs
    /// connected to no declared input, output, or fixed constant.
    pub fn floating_components(&self) -> Vec<usize> {
        self.components
            .iter()
            .enumerate()
            .filter_map(|(index, component)| component.is_floating().then_some(index))
            .collect()
    }

    /// Returns indices into [`components`](Self::components) for subgraphs
    /// containing a declared output but no declared input dependency path.
    ///
    /// A constant output may legitimately appear here when the component
    /// [`touches_one`](ConnectedSubgraph::touches_one); callers decide whether
    /// that is allowed by the circuit specification.
    pub fn output_components_without_inputs(&self) -> Vec<usize> {
        self.components
            .iter()
            .enumerate()
            .filter_map(|(index, component)| {
                (!component.outputs.is_empty() && component.inputs.is_empty()).then_some(index)
            })
            .collect()
    }
}

/// Exact component-local Jacobian rank/nullity coverage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComponentRankReport {
    /// Components checked by exact dense elimination.
    pub checked_components: usize,
    /// Components with no non-free wire and therefore no derived direction to
    /// check.
    pub advice_only_components: usize,
    /// Components skipped because their derived-wire count exceeded the cap.
    pub skipped_components: usize,
    /// Derived wires covered by exact elimination.
    pub checked_derived_wires: usize,
    /// Derived wires omitted because their components exceeded the cap.
    pub skipped_derived_wires: usize,
    /// Derived wires that can move in the Jacobian null space while all
    /// declared free wires are fixed.
    pub movable: Vec<usize>,
}

/// Builds connected components of a recorded circuit graph.
///
/// Every `Lin`, `Gate`, `Enforce`, and `Extra` event connects its algebraically
/// present non-ONE wires. Repeated linear terms and the output's implicit
/// coefficient are combined first so coefficients that cancel cannot create a
/// false dependency path. The fixed wire `0` is treated as an anchor rather
/// than a universal bridge, preserving independent constant-anchored
/// subgraphs. Isolated allocated wires are retained as singleton components.
///
/// # Panics
///
/// Panics when an event or declared boundary references a wire outside
/// `0..wire_count`, or when ONE is declared as an input or output.
pub fn analyze_connectivity<F: Field>(
    events: &[Event<F>],
    wire_count: usize,
    inputs: &[usize],
    outputs: &[usize],
) -> ConnectivityReport {
    assert!(wire_count > 0, "the fixed ONE wire must exist");
    let mut sets = DisjointSet::new(wire_count);
    let mut event_wires = Vec::with_capacity(events.len());

    for (event_index, event) in events.iter().enumerate() {
        let wires = wires_of(event);
        for &wire in &wires {
            assert!(
                wire < wire_count,
                "event {event_index} references wire {wire}, but only {wire_count} wires exist",
            );
        }
        let mut nonconstant = wires.iter().copied().filter(|wire| *wire != 0);
        if let Some(first) = nonconstant.next() {
            for wire in nonconstant {
                sets.union(first, wire);
            }
        }
        event_wires.push(wires);
    }

    for (kind, boundary) in [("input", inputs), ("output", outputs)] {
        for &wire in boundary {
            assert!(wire != 0, "the fixed ONE wire cannot be a declared {kind}");
            assert!(
                wire < wire_count,
                "declared {kind} wire {wire} is outside 0..{wire_count}",
            );
        }
    }

    let mut components = BTreeMap::<usize, ConnectedSubgraph>::new();
    for wire in 1..wire_count {
        let root = sets.find(wire);
        components
            .entry(root)
            .or_insert_with(|| ConnectedSubgraph {
                wires: Vec::new(),
                events: Vec::new(),
                inputs: Vec::new(),
                outputs: Vec::new(),
                touches_one: false,
            })
            .wires
            .push(wire);
    }

    let mut constant_only_events = Vec::new();
    for (event_index, wires) in event_wires.iter().enumerate() {
        if let Some(wire) = wires.iter().copied().find(|wire| *wire != 0) {
            let root = sets.find(wire);
            let component = components
                .get_mut(&root)
                .expect("every non-ONE wire has a component");
            component.events.push(event_index);
            component.touches_one |= wires.contains(&0);
        } else {
            constant_only_events.push(event_index);
        }
    }

    for &wire in inputs {
        let root = sets.find(wire);
        components
            .get_mut(&root)
            .expect("every input has a component")
            .inputs
            .push(wire);
    }
    for &wire in outputs {
        let root = sets.find(wire);
        components
            .get_mut(&root)
            .expect("every output has a component")
            .outputs
            .push(wire);
    }

    for component in components.values_mut() {
        component.inputs.sort_unstable();
        component.inputs.dedup();
        component.outputs.sort_unstable();
        component.outputs.dedup();
    }

    let mut components: Vec<_> = components.into_values().collect();
    components.sort_by_key(|component| component.wires[0]);
    ConnectivityReport {
        wire_count,
        components,
        constant_only_events,
    }
}

/// Runs exact Jacobian rank/nullity analysis independently on connected
/// components with at most `max_derived_wires` non-free wires.
///
/// Splitting prevents unrelated subgraphs from inflating the dense matrix and
/// makes skipped coverage explicit. The returned [`ComponentRankReport`]
/// distinguishes a clean checked component from a component that was too
/// large to analyze; callers must not treat skipped coverage as a clean rank
/// result.
///
/// As with [`underconstrained_derived`], rank is evaluated at `values`:
/// special witnesses can lower the Jacobian rank and should be resampled or
/// reviewed before treating a movable direction as a confirmed bug.
///
/// # Panics
///
/// Panics if `values` does not match the graph's wire count, a free wire is out
/// of range, or `max_derived_wires` is zero.
pub fn analyze_component_rank<F: Field>(
    events: &[Event<F>],
    values: &[F],
    free: &[usize],
    connectivity: &ConnectivityReport,
    max_derived_wires: usize,
) -> ComponentRankReport {
    assert!(max_derived_wires > 0, "the rank cap must be nonzero");
    assert_eq!(
        values.len(),
        connectivity.wire_count,
        "rank values and connectivity must describe the same wires",
    );
    let mut is_free = vec![false; values.len()];
    for &wire in free {
        assert!(wire < values.len(), "free wire {wire} is out of range");
        is_free[wire] = true;
    }

    let mut report = ComponentRankReport {
        checked_components: 0,
        advice_only_components: 0,
        skipped_components: 0,
        checked_derived_wires: 0,
        skipped_derived_wires: 0,
        movable: Vec::new(),
    };
    let mut in_component = vec![false; values.len()];

    for component in &connectivity.components {
        let derived = component
            .wires
            .iter()
            .filter(|&&wire| !is_free[wire])
            .count();
        if derived == 0 {
            report.advice_only_components += 1;
            continue;
        }
        if derived > max_derived_wires {
            report.skipped_components += 1;
            report.skipped_derived_wires += derived;
            continue;
        }

        for &wire in &component.wires {
            in_component[wire] = true;
        }
        let fixed: Vec<usize> = (1..values.len())
            .filter(|&wire| !in_component[wire] || is_free[wire])
            .collect();
        report
            .movable
            .extend(underconstrained_derived(events, values, &fixed));
        for &wire in &component.wires {
            in_component[wire] = false;
        }
        report.checked_components += 1;
        report.checked_derived_wires += derived;
    }

    report.movable.sort_unstable();
    report.movable.dedup();
    report
}

fn wires_of<F: Field>(event: &Event<F>) -> Vec<usize> {
    match event {
        // A `Lin` event records `out = sum(terms)`, so `out` contributes an
        // implicit -1 coefficient to the corresponding zero equality.
        Event::Lin { out, terms } => {
            normalized_term_wires(std::iter::once((*out, -F::ONE)).chain(terms.iter().copied()))
        }
        Event::Gate { a, b, c } => vec![*a, *b, *c],
        Event::Enforce { terms } => normalized_term_wires(terms.iter().copied()),
        Event::Extra { c, d } => vec![*c, *d],
    }
}

/// Returns the wires with a nonzero net coefficient. The recorder drops each
/// individually-zero term, but the same wire can still be added more than once
/// with coefficients that cancel. Such a syntactic mention is not an algebraic
/// dependency and must not join otherwise independent components.
fn normalized_term_wires<F: Field>(terms: impl IntoIterator<Item = (usize, F)>) -> Vec<usize> {
    let mut coefficients = BTreeMap::<usize, F>::new();
    for (wire, coefficient) in terms {
        *coefficients.entry(wire).or_insert(F::ZERO) += coefficient;
    }
    coefficients
        .into_iter()
        .filter_map(|(wire, coefficient)| (coefficient != F::ZERO).then_some(wire))
        .collect()
}

struct DisjointSet {
    parent: Vec<usize>,
}

impl DisjointSet {
    fn new(len: usize) -> Self {
        Self {
            parent: (0..len).collect(),
        }
    }

    fn find(&mut self, wire: usize) -> usize {
        let mut root = wire;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        let mut cursor = wire;
        while self.parent[cursor] != cursor {
            let next = self.parent[cursor];
            self.parent[cursor] = root;
            cursor = next;
        }
        root
    }

    fn union(&mut self, left: usize, right: usize) {
        let left = self.find(left);
        let right = self.find(right);
        if left < right {
            self.parent[right] = left;
        } else if right < left {
            self.parent[left] = right;
        }
    }
}

#[cfg(test)]
mod tests {
    use ragu_arithmetic::ff::Field;
    use ragu_pasta::Fp;

    use super::*;

    #[test]
    fn connectivity_keeps_floating_and_isolated_subgraphs_visible() {
        let events = vec![
            Event::Lin {
                out: 2,
                terms: vec![(1, Fp::ONE)],
            },
            Event::Gate { a: 3, b: 4, c: 5 },
        ];
        let report = analyze_connectivity(&events, 8, &[1], &[2, 7]);

        assert_eq!(
            report.components,
            vec![
                ConnectedSubgraph {
                    wires: vec![1, 2],
                    events: vec![0],
                    inputs: vec![1],
                    outputs: vec![2],
                    touches_one: false,
                },
                ConnectedSubgraph {
                    wires: vec![3, 4, 5],
                    events: vec![1],
                    inputs: vec![],
                    outputs: vec![],
                    touches_one: false,
                },
                ConnectedSubgraph {
                    wires: vec![6],
                    events: vec![],
                    inputs: vec![],
                    outputs: vec![],
                    touches_one: false,
                },
                ConnectedSubgraph {
                    wires: vec![7],
                    events: vec![],
                    inputs: vec![],
                    outputs: vec![7],
                    touches_one: false,
                },
            ],
        );
        assert_eq!(report.isolated_wires(), vec![6, 7]);
        assert_eq!(report.floating_components(), vec![1, 2]);
        assert_eq!(report.output_components_without_inputs(), vec![3]);
    }

    #[test]
    fn one_anchors_without_joining_independent_components() {
        let events = vec![
            Event::Lin {
                out: 1,
                terms: vec![(0, Fp::ONE)],
            },
            Event::Lin {
                out: 2,
                terms: vec![(0, -Fp::ONE)],
            },
            Event::Enforce {
                terms: vec![(0, Fp::ONE)],
            },
        ];
        let report = analyze_connectivity(&events, 3, &[], &[]);

        assert_eq!(report.components.len(), 2);
        assert!(
            report
                .components
                .iter()
                .all(|component| component.touches_one)
        );
        assert!(report.floating_components().is_empty());
        assert_eq!(report.constant_only_events, vec![2]);
    }

    #[test]
    fn cancelled_terms_do_not_create_an_input_output_path() {
        // Algebraically this is `wire 2 = 0`; wire 1 has no influence on the
        // output even though it appears twice in the raw event.
        let events = vec![Event::Lin {
            out: 2,
            terms: vec![(1, Fp::ONE), (1, -Fp::ONE)],
        }];
        let report = analyze_connectivity(&events, 3, &[1], &[2]);

        assert_eq!(report.isolated_wires(), vec![1]);
        assert_eq!(report.output_components_without_inputs(), vec![1]);
        assert_eq!(report.components[1].wires, vec![2]);
        assert_eq!(report.components[1].events, vec![0]);
    }

    #[test]
    fn linear_output_cancellation_does_not_create_a_dependency_path() {
        // `wire 2 = wire 1 + wire 2` constrains only wire 1. The output is not
        // algebraically present after its implicit coefficient is combined.
        let events = vec![Event::Lin {
            out: 2,
            terms: vec![(1, Fp::ONE), (2, Fp::ONE)],
        }];
        let report = analyze_connectivity(&events, 3, &[1], &[2]);

        assert_eq!(report.isolated_wires(), vec![2]);
        assert_eq!(report.output_components_without_inputs(), vec![1]);
        assert_eq!(report.components[0].wires, vec![1]);
        assert_eq!(report.components[0].events, vec![0]);
    }

    #[test]
    fn component_rank_finds_an_unconstrained_derived_wire() {
        let events = vec![Event::Lin {
            out: 2,
            terms: vec![(1, Fp::ONE)],
        }];
        let values = vec![Fp::ONE, Fp::from(3), Fp::from(3), Fp::from(9)];
        let connectivity = analyze_connectivity(&events, values.len(), &[1], &[2]);

        let rank = analyze_component_rank(&events, &values, &[1], &connectivity, 8);
        assert_eq!(rank.checked_components, 2);
        assert_eq!(rank.checked_derived_wires, 2);
        assert_eq!(rank.movable, vec![3]);

        let capped = analyze_component_rank(&events, &values, &[], &connectivity, 1);
        assert_eq!(capped.checked_components, 1);
        assert_eq!(capped.skipped_components, 1);
        assert_eq!(capped.skipped_derived_wires, 2);
        assert_eq!(capped.movable, vec![3]);
    }
}
