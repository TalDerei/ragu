//! Mock equivalents of ragu's enforce-only polynomial relation free functions.

use ff::Field as _;
use pasta_curves::Fp;

use crate::{
    ctx::StepCtx,
    error::{Error, Result},
    polynomial::{Commitment, Polynomial},
};

pub fn enforce_poly_product(
    ctx: &mut StepCtx<'_>,
    multiplicand: &Polynomial,
    multiplier: &Polynomial,
    product_com_witness: Commitment,
) -> Result<Polynomial> {
    let product = multiplicand.multiply(multiplier);
    if product_com_witness != product.commit(Fp::ZERO) {
        return Err(Error("poly product: product commitment witness mismatch"));
    }

    let multiplicand_com = multiplicand.commit(Fp::ZERO);
    let multiplier_com = multiplier.commit(Fp::ZERO);
    let z = ctx.derive_challenge(&[multiplicand_com, multiplier_com, product_com_witness])?;

    ctx.enforce_poly_query(multiplicand_com, z, multiplicand.eval(z))?;
    ctx.enforce_poly_query(multiplier_com, z, multiplier.eval(z))?;
    ctx.enforce_poly_query(product_com_witness, z, product.eval(z))?;

    Ok(product)
}

pub fn enforce_poly_concat(
    ctx: &mut StepCtx<'_>,
    head: &Polynomial,
    tail: &Polynomial,
    offset: usize,
    result: &Polynomial,
    result_com_witness: Commitment,
) -> Result<()> {
    if result_com_witness != result.commit(Fp::ZERO) {
        return Err(Error("poly concat: result commitment witness mismatch"));
    }

    let head_com = head.commit(Fp::ZERO);
    let tail_com = tail.commit(Fp::ZERO);
    let z = ctx.derive_challenge(&[head_com, tail_com, result_com_witness])?;

    let zo = z.pow_vartime([offset as u64]);
    if result.eval(z) != head.eval(z) + zo * tail.eval(z) {
        return Err(Error(
            "poly concat: shifted-sum identity fails at challenge",
        ));
    }

    ctx.enforce_poly_query(head_com, z, head.eval(z))?;
    ctx.enforce_poly_query(tail_com, z, tail.eval(z))?;
    ctx.enforce_poly_query(result_com_witness, z, result.eval(z))?;

    Ok(())
}

pub fn enforce_poly_splice(
    ctx: &mut StepCtx<'_>,
    left: &Polynomial,
    mid_scalar: Fp,
    right: &Polynomial,
    offset: usize,
    result: &Polynomial,
    result_com_witness: Commitment,
) -> Result<()> {
    if result_com_witness != result.commit(Fp::ZERO) {
        return Err(Error("poly splice: result commitment witness mismatch"));
    }

    let left_com = left.commit(Fp::ZERO);
    let right_com = right.commit(Fp::ZERO);
    let z = ctx.derive_challenge(&[left_com, right_com, result_com_witness])?;

    let zo = z.pow_vartime([offset as u64]);
    if result.eval(z) != left.eval(z) + zo * mid_scalar + zo * z * right.eval(z) {
        return Err(Error(
            "poly splice: spliced-sum identity fails at challenge",
        ));
    }

    ctx.enforce_poly_query(left_com, z, left.eval(z))?;
    ctx.enforce_poly_query(right_com, z, right.eval(z))?;
    ctx.enforce_poly_query(result_com_witness, z, result.eval(z))?;

    Ok(())
}
