//! Witness-free source-shape analysis for the fuzz harness.
//!
//! This module intentionally lives in the standalone `qa/fuzz` workspace.
//! It executes generic [`Circuit`] code with an [`Empty`] driver, so witness
//! assignment closures cannot run, and compares the emitted shape with a
//! concrete patcher capture. Nothing is added to a production crate's API.

use ragu_arithmetic::{Coeff, ff::Field};
use ragu_circuits::Circuit;
use ragu_core::{
    Result,
    drivers::{Driver, DriverTypes, LinearExpression},
    maybe::Empty,
};
use ragu_primitives::{Element, GadgetExt};
use ragu_testing::patcher::{Capture, Event};

/// Constraint shape produced by witness-free execution of circuit source.
#[derive(Clone, Debug)]
pub struct SourceShape<F> {
    wire_count: usize,
    events: Vec<Event<F>>,
    outputs: Vec<usize>,
}

impl<F: Field> SourceShape<F> {
    /// Compares this witness-free shape with a concrete synthesis capture.
    pub fn compare(&self, concrete: &Capture<F>) -> SourceLintReport {
        let events = &concrete.recorder.events;
        let first_event_mismatch = self
            .events
            .iter()
            .zip(events)
            .position(|(left, right)| !events_equal(left, right))
            .or_else(|| {
                (self.events.len() != events.len()).then_some(events.len().min(self.events.len()))
            });
        let first_output_mismatch = self
            .outputs
            .iter()
            .zip(&concrete.instance)
            .position(|(left, right)| left != right)
            .or_else(|| {
                (self.outputs.len() != concrete.instance.len())
                    .then_some(self.outputs.len().min(concrete.instance.len()))
            });

        SourceLintReport {
            witness_free_wires: self.wire_count,
            concrete_wires: concrete.recorder.values.len(),
            witness_free_events: self.events.len(),
            concrete_events: events.len(),
            witness_free_outputs: self.outputs.len(),
            concrete_outputs: concrete.instance.len(),
            first_event_mismatch,
            first_output_mismatch,
        }
    }
}

/// Comparison between witness-free circuit shape and concrete synthesis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceLintReport {
    /// Wires allocated by witness-free analysis.
    pub witness_free_wires: usize,
    /// Wires allocated by concrete synthesis.
    pub concrete_wires: usize,
    /// Events emitted by witness-free analysis.
    pub witness_free_events: usize,
    /// Events emitted by concrete synthesis.
    pub concrete_events: usize,
    /// Public-output elements emitted by witness-free analysis.
    pub witness_free_outputs: usize,
    /// Public-output elements emitted by concrete synthesis.
    pub concrete_outputs: usize,
    /// First differing event index, including a missing trailing event.
    pub first_event_mismatch: Option<usize>,
    /// First differing output index, including a missing trailing output.
    pub first_output_mismatch: Option<usize>,
}

impl SourceLintReport {
    /// Returns `true` when wire, event, and output shapes match exactly.
    pub fn is_clean(&self) -> bool {
        self.witness_free_wires == self.concrete_wires
            && self.first_event_mismatch.is_none()
            && self.first_output_mismatch.is_none()
    }
}

/// Executes a circuit with a witness-free driver and records its exact shape.
pub fn analyze_source_shape<F: Field, C: Circuit<F>>(circuit: &C) -> Result<SourceShape<F>> {
    let mut recorder = ShapeRecorder::<F>::new();
    let output = circuit.witness(&mut recorder, Empty)?.into_output();
    let mut buffer: Vec<Element<'_, ShapeRecorder<F>>> = Vec::new();
    output.write(&mut recorder, &mut buffer)?;
    let outputs = buffer.iter().map(|element| *element.wire()).collect();
    Ok(SourceShape {
        wire_count: recorder.wire_count,
        events: recorder.events,
        outputs,
    })
}

fn events_equal<F: Field>(left: &Event<F>, right: &Event<F>) -> bool {
    match (left, right) {
        (
            Event::Lin {
                out: left_out,
                terms: left_terms,
            },
            Event::Lin {
                out: right_out,
                terms: right_terms,
            },
        ) => left_out == right_out && left_terms == right_terms,
        (
            Event::Gate {
                a: left_a,
                b: left_b,
                c: left_c,
            },
            Event::Gate {
                a: right_a,
                b: right_b,
                c: right_c,
            },
        ) => left_a == right_a && left_b == right_b && left_c == right_c,
        (Event::Enforce { terms: left_terms }, Event::Enforce { terms: right_terms }) => {
            left_terms == right_terms
        }
        (
            Event::Extra {
                c: left_c,
                d: left_d,
            },
            Event::Extra {
                c: right_c,
                d: right_d,
            },
        ) => left_c == right_c && left_d == right_d,
        _ => false,
    }
}

struct ShapeLc<F> {
    terms: Vec<(usize, F)>,
    gain: F,
}

impl<F: Field> Default for ShapeLc<F> {
    fn default() -> Self {
        Self {
            terms: Vec::new(),
            gain: F::ONE,
        }
    }
}

impl<F: Field> LinearExpression<usize, F> for ShapeLc<F> {
    fn add_term(mut self, wire: &usize, coefficient: Coeff<F>) -> Self {
        let coefficient = coefficient.value() * self.gain;
        if coefficient != F::ZERO {
            self.terms.push((*wire, coefficient));
        }
        self
    }

    fn gain(mut self, coefficient: Coeff<F>) -> Self {
        self.gain *= coefficient.value();
        self
    }
}

struct ShapeRecorder<F> {
    wire_count: usize,
    events: Vec<Event<F>>,
}

impl<F: Field> ShapeRecorder<F> {
    fn new() -> Self {
        Self {
            wire_count: 1,
            events: Vec::new(),
        }
    }

    fn push_wire(&mut self) -> usize {
        let wire = self.wire_count;
        self.wire_count += 1;
        wire
    }
}

impl<F: Field> DriverTypes for ShapeRecorder<F> {
    type ImplField = F;
    type ImplWire = usize;
    type MaybeKind = Empty;
    type LCadd = ShapeLc<F>;
    type LCenforce = ShapeLc<F>;
    type Extra = usize;

    fn gate(
        &mut self,
        _: impl Fn() -> Result<(Coeff<F>, Coeff<F>, Coeff<F>)>,
    ) -> Result<(usize, usize, usize, usize)> {
        let a = self.push_wire();
        let b = self.push_wire();
        let c = self.push_wire();
        self.events.push(Event::Gate { a, b, c });
        Ok((a, b, c, c))
    }

    fn assign_extra(&mut self, c: usize, _: impl Fn() -> Result<Coeff<F>>) -> Result<usize> {
        let d = self.push_wire();
        self.events.push(Event::Extra { c, d });
        Ok(d)
    }
}

impl<'dr, F: Field> Driver<'dr> for ShapeRecorder<F> {
    type F = F;
    type Wire = usize;
    const ONE: usize = 0;

    fn add(&mut self, expression: impl Fn(ShapeLc<F>) -> ShapeLc<F>) -> usize {
        let expression = expression(ShapeLc::default());
        let out = self.push_wire();
        self.events.push(Event::Lin {
            out,
            terms: expression.terms,
        });
        out
    }

    fn enforce_zero(&mut self, expression: impl Fn(ShapeLc<F>) -> ShapeLc<F>) -> Result<()> {
        let expression = expression(ShapeLc::default());
        self.events.push(Event::Enforce {
            terms: expression.terms,
        });
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use ragu_circuits::WithAux;
    use ragu_core::{drivers::DriverValue, gadgets::Bound};
    use ragu_pasta::Fp;
    use ragu_testing::patcher::capture;

    use super::*;

    struct WitnessDependentShape;

    impl Circuit<Fp> for WitnessDependentShape {
        type Instance<'instance> = ();
        type Output = ();
        type Witness<'witness> = ();
        type Aux<'witness> = ();

        fn instance<'dr, 'instance: 'dr, D: Driver<'dr, F = Fp>>(
            &self,
            _dr: &mut D,
            _instance: DriverValue<D, Self::Instance<'instance>>,
        ) -> Result<Bound<'dr, D, Self::Output>> {
            Ok(())
        }

        fn witness<'dr, 'witness: 'dr, D: Driver<'dr, F = Fp>>(
            &self,
            dr: &mut D,
            _witness: DriverValue<D, Self::Witness<'witness>>,
        ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'witness>>>>
        {
            let _ = dr.mul(|| {
                Err(ragu_core::Error::InvalidWitness(
                    "deliberately swallowed".into(),
                ))
            });
            Ok(WithAux::new((), D::unit()))
        }
    }

    #[test]
    fn detects_witness_dependent_allocation_shape() -> Result<()> {
        let capture = capture(&WitnessDependentShape, ())?;
        let report = analyze_source_shape(&WitnessDependentShape)?.compare(&capture);

        assert!(!report.is_clean());
        assert_eq!(report.witness_free_wires, 4);
        assert_eq!(report.concrete_wires, 1);
        assert_eq!(report.first_event_mismatch, Some(0));
        Ok(())
    }

    struct EqualCountShapeDrift;

    impl Circuit<Fp> for EqualCountShapeDrift {
        type Instance<'instance> = ();
        type Output = ();
        type Witness<'witness> = ();
        type Aux<'witness> = ();

        fn instance<'dr, 'instance: 'dr, D: Driver<'dr, F = Fp>>(
            &self,
            _dr: &mut D,
            _instance: DriverValue<D, Self::Instance<'instance>>,
        ) -> Result<Bound<'dr, D, Self::Output>> {
            Ok(())
        }

        fn witness<'dr, 'witness: 'dr, D: Driver<'dr, F = Fp>>(
            &self,
            dr: &mut D,
            _witness: DriverValue<D, Self::Witness<'witness>>,
        ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'witness>>>>
        {
            let assignment_ran = Cell::new(false);
            let (_, _, zero) = dr.mul(|| {
                assignment_ran.set(true);
                Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero))
            })?;
            let coefficient = if assignment_ran.get() {
                Coeff::One
            } else {
                Coeff::NegativeOne
            };
            dr.enforce_zero(|expression| expression.add_term(&zero, coefficient))?;
            Ok(WithAux::new((), D::unit()))
        }
    }

    #[test]
    fn compares_exact_events_not_only_counts() -> Result<()> {
        let capture = capture(&EqualCountShapeDrift, ())?;
        let report = analyze_source_shape(&EqualCountShapeDrift)?.compare(&capture);

        assert_eq!(report.witness_free_wires, report.concrete_wires);
        assert_eq!(report.witness_free_events, report.concrete_events);
        assert_eq!(report.first_event_mismatch, Some(1));
        assert!(!report.is_clean());
        Ok(())
    }
}
