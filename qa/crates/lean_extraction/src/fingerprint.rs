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

/// Compute the canonical fingerprint of an extracted trace, as a lowercase
/// hex digest.
pub fn digest_hex<F: PrimeField>(input_len: usize, ops: &[Op<F>], outputs: &[Expr<F>]) -> String {
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

    sha256(&buf).iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use ff::PrimeField;
    use ragu_pasta::{Fp, Fq};

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
