use core::marker::PhantomData;

use ff::{FromUniformBytes, PrimeField};
use ragu_core::{
    convert::WireMap,
    drivers::{Driver, DriverTypes},
    gadgets::Gadget,
};

use crate::{
    driver::ExtractionDriver,
    expr::{Expr, Op},
    polynomial::{EvaluationDriver, MAX_DEGREE_BOUND, Record},
};

/// The deliberately small driver extension needed by FV instances.
///
/// Gadget bodies remain generic over Ragu's production [`Driver`] API. This
/// extension only supplies the symbolic public inputs that the FV harness adds
/// around a gadget. Both the exact trace extractor and the direct randomized
/// evaluator implement it.
pub trait InstanceDriver<'dr>: Driver<'dr> {
    /// Allocate `n` verifier-visible input coordinates.
    fn alloc_input_wires(&mut self, n: usize) -> Vec<Self::Wire>;
}

impl<'dr, F: PrimeField> InstanceDriver<'dr> for ExtractionDriver<F> {
    fn alloc_input_wires(&mut self, n: usize) -> Vec<Self::Wire> {
        ExtractionDriver::alloc_input_wires(self, n)
    }
}

/// A [`WireMap`] that collects all physical wires from a gadget by cloning
/// them into a flat [`Vec`].
///
/// Used by [`CircuitInstance`] implementers to manually serialize the output
/// of a circuit into a list of driver wires.
pub struct WireCollector<D: DriverTypes> {
    wires: Vec<D::ImplWire>,
}

impl<D: DriverTypes> WireCollector<D> {
    /// Traverse `gadget` in its declared wire order and return those wires.
    pub fn collect_from<'dr, G>(gadget: &G) -> ragu_core::Result<Vec<D::ImplWire>>
    where
        D: Driver<'dr>,
        G: Gadget<'dr, D>,
    {
        let mut collector = Self { wires: Vec::new() };
        gadget.map(&mut collector)?;
        Ok(collector.wires)
    }
}

impl<D: DriverTypes> WireMap<D::ImplField> for WireCollector<D> {
    type Src = D;
    type Dst = PhantomData<D::ImplField>;

    fn convert_wire(&mut self, wire: &D::ImplWire) -> ragu_core::Result<()> {
        self.wires.push(wire.clone());
        Ok(())
    }
}

/// The inverse of [`WireCollector`]: maps a flat vector of wires back into a
/// gadget, using a template gadget to drive the traversal structure.
pub struct WireDeserializer<D: DriverTypes> {
    wires: std::vec::IntoIter<D::ImplWire>,
}

impl<D: DriverTypes> WireDeserializer<D> {
    pub(crate) fn new(wires: Vec<D::ImplWire>) -> Self {
        Self {
            wires: wires.into_iter(),
        }
    }

    /// Replace the template's wires, in traversal order, with this vector.
    pub fn into_gadget<'dr, G>(mut self, template: &G) -> ragu_core::Result<G>
    where
        D: Driver<'dr>,
        G: Gadget<'dr, D>,
    {
        let actual = self.wires.len();
        let expected = template.num_wires()?;
        if actual != expected {
            return Err(ragu_core::Error::VectorLengthMismatch { expected, actual });
        }
        template.map(&mut self)
    }
}

impl<D: DriverTypes> WireMap<D::ImplField> for WireDeserializer<D> {
    type Src = D;
    type Dst = D;

    fn convert_wire(&mut self, _src: &D::ImplWire) -> ragu_core::Result<D::ImplWire> {
        self.wires
            .next()
            .ok_or_else(|| ragu_core::Error::InvalidWitness("WireDeserializer exhausted".into()))
    }
}

/// A circuit's extracted trace: its input wire count, recorded operations,
/// and output wires.
pub struct ExtractedTrace<F: PrimeField> {
    pub input_len: usize,
    pub ops: Vec<Op<F>>,
    pub outputs: Vec<Expr<F>>,
}

/// One concrete invocation of a deployed gadget enrolled in FV.
pub trait CircuitInstance {
    type Field: PrimeField + FromUniformBytes<64>;

    /// Run the real gadget code on any FV driver and serialize its outputs.
    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Self::Field>;

    /// Run the circuit on the exact symbolic extractor.
    fn extracted_trace() -> ExtractedTrace<Self::Field> {
        let mut dr = ExtractionDriver::<Self::Field>::new();
        let outputs = Self::circuit(&mut dr).expect("circuit failed");
        ExtractedTrace {
            input_len: dr.input_wire_count(),
            ops: dr.ops,
            outputs,
        }
    }

    /// Compute the canonical SHA-256 fingerprint of the extracted trace.
    fn fingerprint() -> String {
        let trace = Self::extracted_trace();
        crate::fingerprint::digest_hex::<Self::Field>(trace.input_len, &trace.ops, &trace.outputs)
    }

    /// Evaluate the production four-slot gate relation directly at `points`
    /// independently derived challenge vectors.
    fn polynomial_record(
        instance: &str,
        seed: [u8; 32],
        points: usize,
    ) -> core::result::Result<Record, String> {
        if points == 0 {
            return Err("polynomial evaluation requires at least one point".to_owned());
        }

        let mut header = None;
        let mut evaluations = Vec::with_capacity(points);
        for point in 0..points {
            let mut dr = EvaluationDriver::<Self::Field>::new(seed, instance, point);
            let outputs = Self::circuit(&mut dr)
                .map_err(|error| format!("{instance}: circuit evaluation failed: {error}"))?;
            let (current_header, evaluation) = dr.finish(&outputs, points);
            if current_header.degree_bound > MAX_DEGREE_BOUND {
                return Err(format!(
                    "{instance}: polynomial degree bound {} exceeds maximum {MAX_DEGREE_BOUND}",
                    current_header.degree_bound
                ));
            }
            if let Some(expected) = &header {
                if expected != &current_header {
                    return Err(format!(
                        "{instance}: structural header changed between evaluation points"
                    ));
                }
            } else {
                header = Some(current_header);
            }
            evaluations.push(evaluation);
        }

        Ok(Record {
            seed,
            header: header.expect("points is nonzero"),
            evaluations,
        })
    }

    /// Differential oracle: evaluate the exact symbolic trace under
    /// the same schedule and reconstruct its implicit production `D` slots.
    #[cfg(test)]
    fn polynomial_trace_record(
        instance: &str,
        seed: [u8; 32],
        points: usize,
    ) -> core::result::Result<Record, String> {
        let trace = Self::extracted_trace();
        crate::polynomial::evaluate_extracted_trace(
            instance,
            seed,
            points,
            trace.input_len,
            &trace.ops,
            &trace.outputs,
        )
    }
}
