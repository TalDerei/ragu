use alloc::{vec, vec::Vec};

use group::{Curve, prime::PrimeCurveAffine};
use pasta_curves::{Ep, EpAffine, Eq, EqAffine, arithmetic::CurveAffine};
use ragu_arithmetic::CurveExt;

const DOMAIN_PREFIX: &str = "Ragu-Parameters";

pub const DEFAULT_EP_K: usize = 13;
pub const DEFAULT_EQ_K: usize = 13;

/// Runtime parameters for the Pasta curve cycle, holding generator points
/// for the Pallas and Vesta curves.
pub struct PastaParams {
    pub(crate) pallas: PallasGenerators,
    pub(crate) vesta: VestaGenerators,
}

/// Fixed generators for one curve of the Pasta cycle.
pub struct Generators<C: CurveAffine> {
    pub(crate) g: Vec<C>,
    pub(crate) w: C,
    pub(crate) u: C,
}

/// Fixed generators for the Pallas curve.
#[allow(dead_code)]
pub type PallasGenerators = Generators<EpAffine>;

/// Fixed generators for the Vesta curve.
#[allow(dead_code)]
pub type VestaGenerators = Generators<EqAffine>;

fn params_for_curve<C: CurveExt>(n: usize) -> (Vec<C::AffineExt>, C::AffineExt, C::AffineExt) {
    let g_projective = {
        let hasher = C::hash_to_curve(DOMAIN_PREFIX);
        let mut g = Vec::with_capacity(n);
        for i in 0..(n as u32) {
            let mut message = [0u8; 5];
            message[1..5].copy_from_slice(&i.to_le_bytes());
            g.push(hasher(&message));
        }
        g
    };
    let mut g = vec![C::AffineExt::identity(); n];
    Curve::batch_normalize(&g_projective[..], &mut g);

    let w: C::AffineExt = C::hash_to_curve(DOMAIN_PREFIX)(&[1]).into();
    let u: C::AffineExt = C::hash_to_curve(DOMAIN_PREFIX)(&[2]).into();

    (g, w, u)
}

impl PastaParams {
    /// Generate Pasta parameters at runtime via hash-to-curve.
    pub(crate) fn generate() -> Self {
        let (ep_g, ep_w, ep_u) = params_for_curve::<Ep>(1usize << DEFAULT_EP_K);
        let (eq_g, eq_w, eq_u) = params_for_curve::<Eq>(1usize << DEFAULT_EQ_K);

        PastaParams {
            pallas: Generators {
                g: ep_g,
                w: ep_w,
                u: ep_u,
            },
            vesta: Generators {
                g: eq_g,
                w: eq_w,
                u: eq_u,
            },
        }
    }
}
