//! Canonical fingerprints of extracted circuit traces.
//!
//! Computes the SHA-256 digest of a canonical byte encoding of a circuit's
//! extracted operation trace and output expressions. The Lean side computes
//! the same digest from the `Clean` reimplementation, and CI compares the
//! two: a match means the reimplementation emits exactly the operations and
//! outputs of the Rust circuit.
//!
//! The byte-level encoding, the input-variable index convention, and the
//! trust assumptions of the check are specified in the FV book
//! (`qa/lean/docs/src/ragu/fingerprint.md`); this module and
//! `qa/lean/Ragu/Fingerprint.lean` implement that spec and must stay in
//! lockstep.

use ff::PrimeField;

use crate::{
    expr::{Expr, Op},
    sha256::sha256,
};

/// Wire index at which encoded input variables start (`2³²`).
pub const INPUT_VAR_OFFSET: u64 = 1 << 32;

/// Domain separator prefixed to every digest preimage.
const DOMAIN_TAG: &[u8] = b"ragu-fv-fingerprint-v1";

fn push_u64(buf: &mut Vec<u8>, n: u64) {
    buf.extend_from_slice(&n.to_le_bytes());
}

/// Append the canonical 32-byte little-endian representation of `value`.
fn push_field_element<F: PrimeField>(buf: &mut Vec<u8>, value: F) {
    let repr = value.to_repr();
    let bytes = repr.as_ref();
    assert_eq!(bytes.len(), 32, "expected a 32-byte field representation");
    buf.extend_from_slice(bytes);
}

/// Append the field modulus as 32 little-endian bytes, parsed from the
/// big-endian hex string [`PrimeField::MODULUS`].
fn push_modulus<F: PrimeField>(buf: &mut Vec<u8>) {
    let hex = F::MODULUS.trim_start_matches("0x");
    assert_eq!(hex.len(), 64, "expected a 256-bit modulus");
    let mut bytes = [0u8; 32];
    for (i, byte) in bytes.iter_mut().rev().enumerate() {
        *byte = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).expect("modulus is valid hex");
    }
    buf.extend_from_slice(&bytes);
}

fn push_expr<F: PrimeField>(buf: &mut Vec<u8>, expr: &Expr<F>) {
    match expr {
        Expr::Var(index) => {
            let index = *index as u64;
            assert!(
                index < INPUT_VAR_OFFSET,
                "wire index {index} collides with the input variable region"
            );
            buf.push(0x01);
            push_u64(buf, index);
        }
        Expr::InputVar(index) => {
            let index = *index as u64;
            assert!(
                index < INPUT_VAR_OFFSET,
                "input variable index {index} overflows the input variable region"
            );
            buf.push(0x01);
            push_u64(buf, INPUT_VAR_OFFSET + index);
        }
        Expr::Const(coeff) => {
            buf.push(0x02);
            push_field_element(buf, coeff.value());
        }
        Expr::Add(left, right) => {
            buf.push(0x03);
            push_expr(buf, left);
            push_expr(buf, right);
        }
        Expr::Mul(left, right) => {
            buf.push(0x04);
            push_expr(buf, left);
            push_expr(buf, right);
        }
    }
}

fn push_op<F: PrimeField>(buf: &mut Vec<u8>, op: &Op<F>) {
    match op {
        Op::Witness { count } => {
            buf.push(0x01);
            push_u64(buf, *count as u64);
        }
        Op::Assert(expr) => {
            buf.push(0x02);
            push_expr(buf, expr);
        }
    }
}

/// Build the canonical digest preimage for an extracted trace.
fn encode_trace<F: PrimeField>(input_len: usize, ops: &[Op<F>], outputs: &[Expr<F>]) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.extend_from_slice(DOMAIN_TAG);
    push_modulus::<F>(&mut buf);
    push_u64(&mut buf, input_len as u64);
    push_u64(&mut buf, outputs.len() as u64);
    push_u64(&mut buf, ops.len() as u64);
    for op in ops {
        push_op(&mut buf, op);
    }
    for output in outputs {
        push_expr(&mut buf, output);
    }
    buf
}

/// Compute the canonical fingerprint of an extracted trace, as a lowercase
/// hex digest.
pub fn digest_hex<F: PrimeField>(input_len: usize, ops: &[Op<F>], outputs: &[Expr<F>]) -> String {
    let buf = encode_trace(input_len, ops, outputs);
    sha256(&buf).iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use ff::PrimeField;
    use ragu_pasta::{Fp, Fq};

    use super::{INPUT_VAR_OFFSET, encode_trace};
    use crate::{
        expr::{Expr, Op},
        instance::CircuitInstance,
    };

    /// Structural mirror of the encoded trace, recovered by [`decode_trace`].
    #[derive(Debug, PartialEq)]
    enum AstExpr {
        Var(u64),
        Const([u8; 32]),
        Add(Box<AstExpr>, Box<AstExpr>),
        Mul(Box<AstExpr>, Box<AstExpr>),
    }

    #[derive(Debug, PartialEq)]
    enum AstOp {
        Witness(u64),
        Assert(AstExpr),
    }

    #[derive(Debug, PartialEq)]
    struct AstTrace {
        modulus: [u8; 32],
        input_len: u64,
        ops: Vec<AstOp>,
        outputs: Vec<AstExpr>,
    }

    /// Strict cursor over the digest preimage; panics on malformed input.
    struct Parser<'a> {
        bytes: &'a [u8],
        pos: usize,
    }

    impl<'a> Parser<'a> {
        fn take(&mut self, n: usize) -> &'a [u8] {
            let slice = &self.bytes[self.pos..self.pos + n];
            self.pos += n;
            slice
        }

        fn byte(&mut self) -> u8 {
            self.take(1)[0]
        }

        fn u64(&mut self) -> u64 {
            u64::from_le_bytes(self.take(8).try_into().unwrap())
        }

        fn bytes32(&mut self) -> [u8; 32] {
            self.take(32).try_into().unwrap()
        }
    }

    fn decode_expr(p: &mut Parser) -> AstExpr {
        match p.byte() {
            0x01 => AstExpr::Var(p.u64()),
            0x02 => AstExpr::Const(p.bytes32()),
            0x03 => AstExpr::Add(Box::new(decode_expr(p)), Box::new(decode_expr(p))),
            0x04 => AstExpr::Mul(Box::new(decode_expr(p)), Box::new(decode_expr(p))),
            tag => panic!("unknown expression tag {tag:#x}"),
        }
    }

    /// Decode a digest preimage produced by [`encode_trace`], asserting that
    /// every byte is consumed.
    fn decode_trace(bytes: &[u8]) -> AstTrace {
        let mut p = Parser { bytes, pos: 0 };
        assert_eq!(p.take(super::DOMAIN_TAG.len()), super::DOMAIN_TAG);
        let modulus = p.bytes32();
        let input_len = p.u64();
        let output_len = p.u64();
        let op_count = p.u64();
        let ops = (0..op_count)
            .map(|_| match p.byte() {
                0x01 => AstOp::Witness(p.u64()),
                0x02 => AstOp::Assert(decode_expr(&mut p)),
                tag => panic!("unknown operation tag {tag:#x}"),
            })
            .collect();
        let outputs = (0..output_len).map(|_| decode_expr(&mut p)).collect();
        assert_eq!(p.pos, bytes.len(), "trailing bytes after outputs");
        AstTrace {
            modulus,
            input_len,
            ops,
            outputs,
        }
    }

    /// Build the AST the decoder is expected to recover, applying the same
    /// trace-to-token mapping rules as the encoder.
    fn expected_expr<F: PrimeField>(expr: &Expr<F>) -> AstExpr {
        match expr {
            Expr::Var(i) => AstExpr::Var(*i as u64),
            Expr::InputVar(i) => AstExpr::Var(INPUT_VAR_OFFSET + *i as u64),
            Expr::Const(c) => {
                let mut buf = Vec::new();
                super::push_field_element(&mut buf, c.value());
                AstExpr::Const(buf.try_into().unwrap())
            }
            Expr::Add(l, r) => AstExpr::Add(
                Box::new(expected_expr(l)),
                Box::new(expected_expr(r)),
            ),
            Expr::Mul(l, r) => AstExpr::Mul(
                Box::new(expected_expr(l)),
                Box::new(expected_expr(r)),
            ),
        }
    }

    /// Encode an instance's trace and decode it back, asserting the decoder
    /// recovers exactly the original trace. This demonstrates that the
    /// encoding is uniquely decodable — and therefore injective — over the
    /// exported corpus.
    fn assert_roundtrip<I: CircuitInstance>() {
        let (input_len, ops, outputs) = I::extracted_trace();
        let decoded = decode_trace(&encode_trace::<I::Field>(input_len, &ops, &outputs));

        let mut modulus = Vec::new();
        super::push_modulus::<I::Field>(&mut modulus);
        let expected = AstTrace {
            modulus: modulus.try_into().unwrap(),
            input_len: input_len as u64,
            ops: ops
                .iter()
                .map(|op| match op {
                    Op::Witness { count } => AstOp::Witness(*count as u64),
                    Op::Assert(expr) => AstOp::Assert(expected_expr(expr)),
                })
                .collect(),
            outputs: outputs.iter().map(expected_expr).collect(),
        };
        assert_eq!(decoded, expected);
    }

    #[test]
    fn encoding_roundtrips_for_every_instance() {
        use crate::instances::{
            boolean_alloc::BooleanAllocInstance,
            boolean_and::BooleanAndInstance,
            boolean_conditional_enforce_equal::BooleanConditionalEnforceEqualInstance,
            boolean_conditional_select::BooleanConditionalSelectInstance,
            core_mul::CoreMulInstance,
            element_alloc::ElementAllocInstance,
            element_alloc_square::ElementAllocSquareInstance,
            element_div_nonzero::ElementDivNonzeroInstance,
            element_enforce_nonzero::ElementEnforceNonzeroInstance,
            element_enforce_root_of_unity::{
                ElementEnforceRootOfUnityInstanceK2, ElementEnforceRootOfUnityInstanceK5,
            },
            element_enforce_zero::ElementEnforceZeroInstance,
            element_fold::{ElementFoldInstanceN3, ElementFoldInstanceN7},
            element_invert::ElementInvertInstance,
            element_invert_with::ElementInvertWithInstance,
            element_is_equal::ElementIsEqualInstance,
            element_is_zero::ElementIsZeroInstance,
            element_mul::ElementMulInstance,
            element_square::ElementSquareInstance,
            nonzero_bank_scope::NonzeroBankScopeInstanceK2,
            point_add_incomplete::PointAddIncompleteInstance,
            point_alloc::{PointAllocInstanceFp, PointAllocInstanceFq},
            point_conditional_endo::PointConditionalEndoInstance,
            point_conditional_negate::PointConditionalNegateInstance,
            point_double::PointDoubleInstance,
            point_double_and_add_incomplete::PointDoubleAndAddIncompleteInstance,
        };

        assert_roundtrip::<PointAllocInstanceFp>();
        assert_roundtrip::<PointAllocInstanceFq>();
        assert_roundtrip::<PointDoubleInstance>();
        assert_roundtrip::<PointDoubleAndAddIncompleteInstance>();
        assert_roundtrip::<PointAddIncompleteInstance>();
        assert_roundtrip::<PointConditionalEndoInstance>();
        assert_roundtrip::<PointConditionalNegateInstance>();
        assert_roundtrip::<ElementMulInstance>();
        assert_roundtrip::<ElementSquareInstance>();
        assert_roundtrip::<ElementAllocInstance>();
        assert_roundtrip::<ElementAllocSquareInstance>();
        assert_roundtrip::<ElementDivNonzeroInstance>();
        assert_roundtrip::<ElementFoldInstanceN3>();
        assert_roundtrip::<ElementFoldInstanceN7>();
        assert_roundtrip::<ElementEnforceRootOfUnityInstanceK2>();
        assert_roundtrip::<ElementEnforceRootOfUnityInstanceK5>();
        assert_roundtrip::<ElementEnforceZeroInstance>();
        assert_roundtrip::<ElementInvertInstance>();
        assert_roundtrip::<ElementInvertWithInstance>();
        assert_roundtrip::<ElementEnforceNonzeroInstance>();
        assert_roundtrip::<NonzeroBankScopeInstanceK2>();
        assert_roundtrip::<ElementIsEqualInstance>();
        assert_roundtrip::<ElementIsZeroInstance>();
        assert_roundtrip::<CoreMulInstance>();
        assert_roundtrip::<BooleanAllocInstance>();
        assert_roundtrip::<BooleanAndInstance>();
        assert_roundtrip::<BooleanConditionalSelectInstance>();
        assert_roundtrip::<BooleanConditionalEnforceEqualInstance>();
    }

    /// The modulus encoding must round-trip through the canonical field
    /// element representation: `-1` is `modulus - 1`.
    #[test]
    fn modulus_matches_repr() {
        fn check<F: PrimeField>() {
            let mut modulus = Vec::new();
            super::push_modulus::<F>(&mut modulus);

            let mut minus_one = Vec::new();
            super::push_field_element(&mut minus_one, -F::ONE);

            // minus_one + 1 == modulus, as 256-bit little-endian integers
            let mut carry = 1u16;
            for byte in &mut minus_one {
                let sum = *byte as u16 + carry;
                *byte = (sum & 0xff) as u8;
                carry = sum >> 8;
            }
            assert_eq!(minus_one, modulus);
        }
        check::<Fp>();
        check::<Fq>();
    }
}
