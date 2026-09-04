use ragu_pasta::Fp;
use ragu_primitives::{Element, NonzeroBank};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireDeserializer},
};

pub struct NonzeroBankScopeInstance<const K: usize>;

/// `K = 0`: an empty scope still discharges, constraining the initial product
/// `1` nonzero. The Lean reimpl splits `K = 0` from `K + 1` (`Fin 0` is not
/// `Inhabited`), so without this instance that branch is never fingerprinted.
pub type NonzeroBankScopeInstanceK0 = NonzeroBankScopeInstance<0>;

/// `K = 1`: a single fold, the smallest case going through the `foldl` body.
pub type NonzeroBankScopeInstanceK1 = NonzeroBankScopeInstance<1>;

pub type NonzeroBankScopeInstanceK2 = NonzeroBankScopeInstance<2>;

impl<const K: usize> CircuitInstance for NonzeroBankScopeInstance<K> {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // Packages a full `NonzeroBank::scope` over `K` factors as a standalone
        // lemma circuit: every fold mul gate + the final discharge. The Lean
        // reimpl spec is that every input factor is nonzero — i.e., the
        // multiplicative-integrality lemma at this `K`.
        let element_template = Element::constant(dr, Fp::zero());

        let mut factors = Vec::with_capacity(K);
        for _ in 0..K {
            let input_wires = dr.alloc_input_wires(1);
            let factor = WireDeserializer::new(input_wires).into_gadget(&element_template)?;
            factors.push(factor);
        }

        NonzeroBank::scope(dr, |dr, bank| {
            for factor in factors {
                bank.fold(dr, factor)?;
            }
            Ok(())
        })?;

        Ok(Vec::new())
    }
}
