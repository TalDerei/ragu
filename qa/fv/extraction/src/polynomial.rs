//! Direct randomized evaluation of the gadget-level polynomial relation.
//!
//! Unlike [`crate::driver::ExtractionDriver`], this driver never constructs an
//! expression DAG. It assigns distinct geometric powers of domain-separated
//! field challenges to verifier inputs and to every `A`, `B`, `C`, and `D`
//! gate slot, then evaluates linear combinations immediately. Ordered gate
//! relations, linear constraints, `assign_extra` uses, and outputs are folded
//! with separate geometric position challenges.

#[cfg(test)]
use std::{collections::HashMap, sync::Arc};

use ff::{FromUniformBytes, PrimeField};
use ragu_arithmetic::Coeff;
use ragu_core::{
    Result,
    drivers::{DirectSum, Driver, DriverTypes},
    maybe::Empty,
};

#[cfg(test)]
use crate::expr::{Expr, Op};
use crate::{instance::FvDriver, sha256::sha256};

/// Version/domain tag shared with `Ragu.PolynomialFingerprint`.
pub const FORMAT_TAG: &str = "ragu-fv-polynomial-v1";

/// Default number of independent evaluations.
///
/// The evaluator rejects an encoded relation whose declared degree exceeds
/// [`MAX_DEGREE_BOUND`]. Two points therefore give a Schwartz--Zippel bound of
/// less than `2^-480` for both Pasta fields. The bound includes the maximum
/// point mass from reducing independent uniform 512-bit random-oracle outputs
/// modulo the field.
pub const DEFAULT_POINTS: usize = 2;

/// Maximum admitted total degree after geometric-sequence substitution.
pub const MAX_DEGREE_BOUND: usize = 2048;

#[derive(Clone)]
struct ChallengeContext {
    seed: [u8; 32],
    modulus_le: [u8; 32],
    instance: String,
    point: usize,
}

impl ChallengeContext {
    fn new<F: PrimeField>(seed: [u8; 32], instance: &str, point: usize) -> Self {
        Self {
            seed,
            modulus_le: modulus_le::<F>(),
            instance: instance.to_owned(),
            point,
        }
    }

    /// Domain-separated 512-bit little-endian integer reduced into `F`.
    fn base<F: FromUniformBytes<64>>(&self, label: &str) -> F {
        let mut wide = [0u8; 64];
        for block in 0..2 {
            let mut preimage = Vec::new();
            preimage.extend_from_slice(FORMAT_TAG.as_bytes());
            preimage.extend_from_slice(&self.seed);
            preimage.extend_from_slice(&self.modulus_le);
            push_len_prefixed(&mut preimage, self.instance.as_bytes());
            preimage.extend_from_slice(&(self.point as u64).to_le_bytes());
            push_len_prefixed(&mut preimage, label.as_bytes());
            preimage.push(block as u8);
            wide[32 * block..32 * (block + 1)].copy_from_slice(&sha256(&preimage));
        }
        F::from_uniform_bytes(&wide)
    }
}

#[derive(Clone)]
struct ChallengeBases<F> {
    input: F,
    wire_a: F,
    wire_b: F,
    wire_c: F,
    wire_d: F,
    gate_ab_weight: F,
    gate_cd_weight: F,
    constraint_weight: F,
    extra_weight: F,
    output_weight: F,
}

impl<F: FromUniformBytes<64>> ChallengeBases<F> {
    fn new(ctx: &ChallengeContext) -> Self {
        Self {
            input: ctx.base("input"),
            wire_a: ctx.base("wire-a"),
            wire_b: ctx.base("wire-b"),
            wire_c: ctx.base("wire-c"),
            wire_d: ctx.base("wire-d"),
            gate_ab_weight: ctx.base("gate-ab-weight"),
            gate_cd_weight: ctx.base("gate-cd-weight"),
            constraint_weight: ctx.base("constraint-weight"),
            extra_weight: ctx.base("extra-weight"),
            output_weight: ctx.base("output-weight"),
        }
    }
}

fn sequence<F: PrimeField>(base: F, index: usize) -> F {
    base.pow_vartime([(index as u64) + 1])
}

fn push_len_prefixed(buf: &mut Vec<u8>, bytes: &[u8]) {
    buf.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    buf.extend_from_slice(bytes);
}

fn modulus_le<F: PrimeField>() -> [u8; 32] {
    let hex = F::MODULUS.trim_start_matches("0x");
    assert_eq!(hex.len(), 64, "expected a 256-bit modulus");
    let mut bytes = [0u8; 32];
    for (i, byte) in bytes.iter_mut().rev().enumerate() {
        *byte = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).expect("modulus is valid hex");
    }
    bytes
}

fn field_hex<F: PrimeField>(value: F) -> String {
    value
        .to_repr()
        .as_ref()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn bytes_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// Exact structural header compared before the randomized values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Header {
    pub instance: String,
    pub modulus: String,
    pub inputs: usize,
    pub outputs: usize,
    pub gates: usize,
    pub gate_relations: usize,
    pub linear_constraints: usize,
    pub assigned_extras: usize,
    pub degree_bound: usize,
    pub points: usize,
}

/// One independently challenged evaluation of the encoded relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PointEvaluation {
    pub gates: String,
    pub constraints: String,
    pub extras: String,
    pub outputs: String,
}

/// Machine-readable record printed as one tab-separated line per instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record {
    pub seed: [u8; 32],
    pub header: Header,
    pub evaluations: Vec<PointEvaluation>,
}

impl Record {
    pub fn line(&self) -> String {
        let evaluations = self
            .evaluations
            .iter()
            .map(|point| {
                format!(
                    "{},{},{},{}",
                    point.gates, point.constraints, point.extras, point.outputs
                )
            })
            .collect::<Vec<_>>()
            .join(";");
        format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            FORMAT_TAG,
            bytes_hex(&self.seed),
            self.header.instance,
            self.header.modulus,
            self.header.inputs,
            self.header.outputs,
            self.header.gates,
            self.header.gate_relations,
            self.header.linear_constraints,
            self.header.assigned_extras,
            self.header.degree_bound,
            self.header.points,
            evaluations,
        )
    }
}

/// Total-degree bound after substituting geometric challenge sequences.
///
/// Gate relations have degree at most `3 * gates`. A linear constraint or
/// output has one position-weight factor and at most one input/gate-slot
/// factor. An assigned extra similarly combines its position weight with its
/// originating `D` slot.
pub fn degree_bound(
    inputs: usize,
    outputs: usize,
    gates: usize,
    constraints: usize,
    extras: usize,
) -> usize {
    let variables = inputs.max(gates);
    gates
        .saturating_mul(3)
        .max(variables.saturating_add(constraints))
        .max(gates.saturating_add(extras))
        .max(variables.saturating_add(outputs))
}

pub struct ExtraWire<F> {
    value: F,
}

/// `Driver` that directly evaluates the complete four-slot gate relation.
pub struct EvaluationDriver<F: PrimeField + FromUniformBytes<64>> {
    challenges: ChallengeContext,
    bases: ChallengeBases<F>,
    next_input: usize,
    gates: usize,
    constraints: usize,
    assigned_extras: usize,
    gate_accumulator: F,
    constraint_accumulator: F,
    extra_accumulator: F,
}

impl<F: PrimeField + FromUniformBytes<64>> EvaluationDriver<F> {
    pub fn new(seed: [u8; 32], instance: &str, point: usize) -> Self {
        let challenges = ChallengeContext::new::<F>(seed, instance, point);
        let bases = ChallengeBases::new(&challenges);
        Self {
            challenges,
            bases,
            next_input: 0,
            gates: 0,
            constraints: 0,
            assigned_extras: 0,
            gate_accumulator: F::ZERO,
            constraint_accumulator: F::ZERO,
            extra_accumulator: F::ZERO,
        }
    }

    pub fn finish(self, outputs: &[F], point_count: usize) -> (Header, PointEvaluation) {
        let mut output_accumulator = F::ZERO;
        for (index, output) in outputs.iter().enumerate() {
            output_accumulator += sequence(self.bases.output_weight, index) * output;
        }

        let header = Header {
            instance: self.challenges.instance.clone(),
            modulus: F::MODULUS.trim_start_matches("0x").to_ascii_lowercase(),
            inputs: self.next_input,
            outputs: outputs.len(),
            gates: self.gates,
            gate_relations: 2 * self.gates,
            linear_constraints: self.constraints,
            assigned_extras: self.assigned_extras,
            degree_bound: degree_bound(
                self.next_input,
                outputs.len(),
                self.gates,
                self.constraints,
                self.assigned_extras,
            ),
            points: point_count,
        };
        let point = PointEvaluation {
            gates: field_hex(self.gate_accumulator),
            constraints: field_hex(self.constraint_accumulator),
            extras: field_hex(self.extra_accumulator),
            outputs: field_hex(output_accumulator),
        };
        (header, point)
    }
}

impl<F: PrimeField + FromUniformBytes<64>> DriverTypes for EvaluationDriver<F> {
    type ImplField = F;
    type ImplWire = F;
    type MaybeKind = Empty;
    type LCadd = DirectSum<F>;
    type LCenforce = DirectSum<F>;
    type Extra = ExtraWire<F>;

    fn gate(
        &mut self,
        _: impl Fn() -> Result<(Coeff<F>, Coeff<F>, Coeff<F>)>,
    ) -> Result<(F, F, F, Self::Extra)> {
        let gate = self.gates;
        let a = sequence(self.bases.wire_a, gate);
        let b = sequence(self.bases.wire_b, gate);
        let c = sequence(self.bases.wire_c, gate);
        let d = sequence(self.bases.wire_d, gate);

        let ab = a * b - c;
        let cd = c * d;
        self.gate_accumulator += sequence(self.bases.gate_ab_weight, gate) * ab;
        self.gate_accumulator += sequence(self.bases.gate_cd_weight, gate) * cd;
        self.gates += 1;

        Ok((a, b, c, ExtraWire { value: d }))
    }

    fn assign_extra(&mut self, extra: Self::Extra, _: impl Fn() -> Result<Coeff<F>>) -> Result<F> {
        let position = self.assigned_extras;
        self.extra_accumulator += sequence(self.bases.extra_weight, position) * extra.value;
        self.assigned_extras += 1;
        Ok(extra.value)
    }
}

impl<'dr, F: PrimeField + FromUniformBytes<64>> Driver<'dr> for EvaluationDriver<F> {
    type F = F;
    type Wire = F;

    const ONE: F = F::ONE;

    fn constant(&mut self, value: Coeff<F>) -> F {
        value.value()
    }

    fn add(&mut self, lc: impl Fn(DirectSum<F>) -> DirectSum<F>) -> F {
        lc(DirectSum::default()).value()
    }

    fn enforce_zero(&mut self, lc: impl Fn(DirectSum<F>) -> DirectSum<F>) -> Result<()> {
        let value = lc(DirectSum::default()).value();
        let position = self.constraints;
        self.constraint_accumulator += sequence(self.bases.constraint_weight, position) * value;
        self.constraints += 1;
        Ok(())
    }
}

impl<'dr, F: PrimeField + FromUniformBytes<64>> FvDriver<'dr> for EvaluationDriver<F> {
    fn alloc_input_wires(&mut self, n: usize) -> Vec<F> {
        let start = self.next_input;
        self.next_input += n;
        (start..start + n)
            .map(|index| sequence(self.bases.input, index))
            .collect()
    }
}

#[cfg(test)]
fn evaluate_expr<F: PrimeField>(
    expr: &Expr<F>,
    bases: &ChallengeBases<F>,
    input_count: usize,
    gate_count: usize,
    memo: &mut HashMap<*const Expr<F>, F>,
) -> core::result::Result<F, String> {
    match expr {
        Expr::Var(index) => {
            if *index >= 3 * gate_count {
                return Err(format!(
                    "local variable {index} is outside {gate_count} three-wire gate encodings"
                ));
            }
            let gate = index / 3;
            Ok(match index % 3 {
                0 => sequence(bases.wire_a, gate),
                1 => sequence(bases.wire_b, gate),
                _ => sequence(bases.wire_c, gate),
            })
        }
        Expr::InputVar(index) => {
            if *index >= input_count {
                return Err(format!(
                    "input variable {index} is outside input arity {input_count}"
                ));
            }
            Ok(sequence(bases.input, *index))
        }
        Expr::Const(coeff) => Ok(coeff.value()),
        Expr::Add(left, right) => Ok(evaluate_shared(left, bases, input_count, gate_count, memo)?
            + evaluate_shared(right, bases, input_count, gate_count, memo)?),
        Expr::Mul(left, right) => Ok(evaluate_shared(left, bases, input_count, gate_count, memo)?
            * evaluate_shared(right, bases, input_count, gate_count, memo)?),
    }
}

#[cfg(test)]
fn evaluate_shared<F: PrimeField>(
    expr: &Arc<Expr<F>>,
    bases: &ChallengeBases<F>,
    input_count: usize,
    gate_count: usize,
    memo: &mut HashMap<*const Expr<F>, F>,
) -> core::result::Result<F, String> {
    let key = Arc::as_ptr(expr);
    if let Some(value) = memo.get(&key) {
        return Ok(*value);
    }
    let value = evaluate_expr(expr, bases, input_count, gate_count, memo)?;
    memo.insert(key, value);
    Ok(value)
}

/// Evaluate the legacy symbolic trace under the new polynomial schedule.
///
/// This is a migration oracle and diagnostic, not the primary evaluator. It
/// decodes every `Witness(3), Assert(...)` pair as one gate, synthesizes the
/// production `D` slot and `C * D` relation, and treats later assertions as
/// linear constraints exactly as the Lean evaluator does.
#[cfg(test)]
pub fn evaluate_extracted_trace<F: PrimeField + FromUniformBytes<64>>(
    instance: &str,
    seed: [u8; 32],
    points: usize,
    input_count: usize,
    ops: &[Op<F>],
    outputs: &[Expr<F>],
) -> core::result::Result<Record, String> {
    if points == 0 {
        return Err("polynomial evaluation requires at least one point".to_owned());
    }

    let mut gate_assertions = Vec::new();
    let mut constraints = Vec::new();
    let mut index = 0;
    while index < ops.len() {
        match &ops[index] {
            Op::Witness { count } => {
                if *count != 3 {
                    return Err(format!(
                        "unsupported witness count {count}; expected a three-wire gate"
                    ));
                }
                let Some(Op::Assert(gate)) = ops.get(index + 1) else {
                    return Err(
                        "a three-wire gate witness was not immediately followed by its gate assertion"
                            .to_owned(),
                    );
                };
                gate_assertions.push(gate);
                index += 2;
            }
            Op::Assert(constraint) => {
                constraints.push(constraint);
                index += 1;
            }
        }
    }

    let gate_count = gate_assertions.len();
    let header = Header {
        instance: instance.to_owned(),
        modulus: F::MODULUS.trim_start_matches("0x").to_ascii_lowercase(),
        inputs: input_count,
        outputs: outputs.len(),
        gates: gate_count,
        gate_relations: 2 * gate_count,
        linear_constraints: constraints.len(),
        assigned_extras: 0,
        degree_bound: degree_bound(input_count, outputs.len(), gate_count, constraints.len(), 0),
        points,
    };
    if header.degree_bound > MAX_DEGREE_BOUND {
        return Err(format!(
            "{instance}: polynomial degree bound {} exceeds maximum {MAX_DEGREE_BOUND}",
            header.degree_bound
        ));
    }
    let mut evaluations = Vec::with_capacity(points);
    for point in 0..points {
        let ctx = ChallengeContext::new::<F>(seed, instance, point);
        let bases = ChallengeBases::new(&ctx);
        let mut memo = HashMap::new();
        let mut gate_accumulator = F::ZERO;
        for (gate, assertion) in gate_assertions.iter().enumerate() {
            let ab = evaluate_expr(assertion, &bases, input_count, gate_count, &mut memo)?;
            let c = sequence(bases.wire_c, gate);
            let d = sequence(bases.wire_d, gate);
            gate_accumulator += sequence(bases.gate_ab_weight, gate) * ab;
            gate_accumulator += sequence(bases.gate_cd_weight, gate) * c * d;
        }
        let mut constraint_accumulator = F::ZERO;
        for (position, constraint) in constraints.iter().enumerate() {
            let value = evaluate_expr(constraint, &bases, input_count, gate_count, &mut memo)?;
            constraint_accumulator += sequence(bases.constraint_weight, position) * value;
        }
        let mut output_accumulator = F::ZERO;
        for (position, output) in outputs.iter().enumerate() {
            let value = evaluate_expr(output, &bases, input_count, gate_count, &mut memo)?;
            output_accumulator += sequence(bases.output_weight, position) * value;
        }
        evaluations.push(PointEvaluation {
            gates: field_hex(gate_accumulator),
            constraints: field_hex(constraint_accumulator),
            extras: field_hex(F::ZERO),
            outputs: field_hex(output_accumulator),
        });
    }

    Ok(Record {
        seed,
        header,
        evaluations,
    })
}

/// Strictly parse a 32-byte lowercase or uppercase hexadecimal seed.
pub fn parse_seed(hex: &str) -> core::result::Result<[u8; 32], String> {
    if hex.len() != 64 {
        return Err(format!(
            "seed must contain exactly 64 hexadecimal digits, got {}",
            hex.len()
        ));
    }
    let mut seed = [0u8; 32];
    for (index, byte) in seed.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[2 * index..2 * index + 2], 16)
            .map_err(|_| format!("seed contains non-hexadecimal digits at byte {index}"))?;
    }
    Ok(seed)
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use ragu_core::drivers::{Driver, DriverTypes, LinearExpression};
    use ragu_pasta::{Fp, Fq};

    use super::*;
    use crate::instance::{CircuitInstance, FvDriver};

    const SEED_HEX: &str = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";

    fn seed() -> [u8; 32] {
        parse_seed(SEED_HEX).expect("fixed test seed is valid")
    }

    #[test]
    fn seed_parser_and_point_count_fail_closed() {
        assert!(parse_seed("").is_err());
        assert!(parse_seed(&"0".repeat(63)).is_err());
        assert!(parse_seed(&"0".repeat(65)).is_err());
        assert!(parse_seed(&format!("{}g", "0".repeat(63))).is_err());
        assert!(EmptyInstance::polynomial_record("empty", seed(), 0).is_err());
    }

    #[test]
    fn challenge_derivation_matches_the_versioned_unit_vectors() {
        let fp: Fp = ChallengeContext::new::<Fp>(seed(), "unit-vector", 7).base("input");
        let fq: Fq = ChallengeContext::new::<Fq>(seed(), "unit-vector", 7).base("input");
        assert_eq!(
            field_hex(fp),
            "84ca68b8355db4099ed6dbec9a5269a27b382bff7463849781790f31a5c8cf20"
        );
        assert_eq!(
            field_hex(fq),
            "76158de890f06f483d739d6475decc6b97033fabf65a8f46eb450f08a5fe2636"
        );
    }

    #[test]
    fn complete_gate_relation_includes_d_and_assign_extra() {
        let mut driver = EvaluationDriver::<Fp>::new(seed(), "four-slot", 0);
        let bases = driver.bases.clone();
        let (a, b, c, extra) = driver
            .gate(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))
            .unwrap();
        let d = driver.assign_extra(extra, || Ok(Coeff::Zero)).unwrap();

        let ab_only = sequence(bases.gate_ab_weight, 0) * (a * b - c);
        let cd_term = sequence(bases.gate_cd_weight, 0) * c * d;
        assert_ne!(cd_term, Fp::ZERO, "fixed seed must exercise C * D");

        let (header, point) = driver.finish(&[d], DEFAULT_POINTS);
        assert_eq!(header.gates, 1);
        assert_eq!(header.gate_relations, 2);
        assert_eq!(header.assigned_extras, 1);
        assert_eq!(point.gates, field_hex(ab_only + cd_term));
        assert_ne!(point.gates, field_hex(ab_only));
        assert_eq!(point.extras, field_hex(sequence(bases.extra_weight, 0) * d));
    }

    #[test]
    fn coefficient_wire_constraint_order_and_output_order_mutations_are_detected() {
        fn evaluate(
            second_coefficient: Coeff<Fp>,
            reverse_constraints: bool,
            reverse_outputs: bool,
        ) -> PointEvaluation {
            let mut driver = EvaluationDriver::<Fp>::new(seed(), "mutation", 0);
            let inputs = driver.alloc_input_wires(2);
            driver
                .enforce_zero(|lc| lc.add(&inputs[0]).add_term(&inputs[1], second_coefficient))
                .unwrap();
            if reverse_constraints {
                driver.enforce_zero(|lc| lc.add(&inputs[0])).unwrap();
                driver.enforce_zero(|lc| lc.add(&inputs[1])).unwrap();
            } else {
                driver.enforce_zero(|lc| lc.add(&inputs[1])).unwrap();
                driver.enforce_zero(|lc| lc.add(&inputs[0])).unwrap();
            }
            let outputs = if reverse_outputs {
                [inputs[1], inputs[0]]
            } else {
                [inputs[0], inputs[1]]
            };
            driver.finish(&outputs, 1).1
        }

        let baseline = evaluate(Coeff::One, false, false);
        assert_ne!(
            baseline.constraints,
            evaluate(Coeff::Two, false, false).constraints
        );
        assert_ne!(
            baseline.constraints,
            evaluate(Coeff::One, true, false).constraints
        );
        assert_ne!(baseline.outputs, evaluate(Coeff::One, false, true).outputs);
    }

    #[test]
    fn unused_gate_changes_the_exact_header_and_gate_evaluation() {
        let empty = EvaluationDriver::<Fp>::new(seed(), "unused-gate", 0).finish(&[], 1);
        let mut changed = EvaluationDriver::<Fp>::new(seed(), "unused-gate", 0);
        changed
            .gate(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))
            .unwrap();
        let changed = changed.finish(&[], 1);
        assert_ne!(empty.0, changed.0);
        assert_ne!(empty.1.gates, changed.1.gates);
    }

    #[test]
    fn a_public_fixed_point_can_be_targeted_but_the_next_point_rejects() {
        let fixed = ChallengeContext::new::<Fp>(seed(), "fixed-point", 0).base("input");

        let evaluate = |point| {
            let mut driver = EvaluationDriver::<Fp>::new(seed(), "fixed-point", point);
            let input = driver.alloc_input_wires(1)[0];
            driver
                .enforce_zero(|lc| {
                    lc.add(&input)
                        .add_term(&Fp::ONE, Coeff::NegativeArbitrary(fixed))
                })
                .unwrap();
            driver.finish(&[], 1).1.constraints
        };

        assert_eq!(evaluate(0), field_hex(Fp::ZERO));
        assert_ne!(evaluate(1), field_hex(Fp::ZERO));
    }

    #[test]
    fn both_pasta_fields_have_distinct_exact_headers() {
        let fp = EvaluationDriver::<Fp>::new(seed(), "field", 0)
            .finish(&[], 1)
            .0;
        let fq = EvaluationDriver::<Fq>::new(seed(), "field", 0)
            .finish(&[], 1)
            .0;
        assert_ne!(fp.modulus, fq.modulus);
        assert!(fp.degree_bound <= MAX_DEGREE_BOUND);
        assert!(fq.degree_bound <= MAX_DEGREE_BOUND);
    }

    #[test]
    fn degree_cap_is_enforced() {
        let error = OversizedInstance::polynomial_record("oversized", seed(), 1).unwrap_err();
        assert!(error.contains("degree bound 2049 exceeds maximum 2048"));
        assert_eq!(degree_bound(usize::MAX, 1, 1, 1, 1), usize::MAX);
    }

    struct EmptyInstance;

    impl CircuitInstance for EmptyInstance {
        type Field = Fp;

        fn circuit<'dr, D>(_: &mut D) -> ragu_core::Result<Vec<D::Wire>>
        where
            D: FvDriver<'dr, F = Self::Field>,
        {
            Ok(Vec::new())
        }
    }

    struct OversizedInstance;

    impl CircuitInstance for OversizedInstance {
        type Field = Fp;

        fn circuit<'dr, D>(driver: &mut D) -> ragu_core::Result<Vec<D::Wire>>
        where
            D: FvDriver<'dr, F = Self::Field>,
        {
            for _ in 0..683 {
                driver.gate(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
            }
            Ok(Vec::new())
        }
    }
}
