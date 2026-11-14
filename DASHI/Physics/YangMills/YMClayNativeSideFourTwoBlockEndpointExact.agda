module DASHI.Physics.YangMills.YMClayNativeSideFourTwoBlockEndpointExact where

------------------------------------------------------------------------
-- R445 original side-four exact finite instance:
--
-- Original 4D periodic fine side 4 (256 sites, 1024 positive bonds),
-- block side 2, coarse side 2 (16 sites, 64 positive coarse links).
--
-- The remaining generic BlockEndpointCompatibility is a single
-- arithmetic assertion. On THIS ACTUAL side-four source, both coarse
-- index values 0 and 1 and all four original axes reduce definitionally
-- through the pre-existing CyclicIndex/Fin/BlockedCube4 codecs.
--
-- Eight cases (2 coordinate values * 4 axes), no new geometry/group.
-- These source-written `refl` terms MUST still pass Agda kernel; no
-- compiler is available here. No extrapolation to all M,L is made.
--
-- This yields the selected finite SU(N) group-valued coarse-link gauge
-- covariance, NOT a Wilson coarse action or Gibbs/RG pushforward.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClayNativeBlockedPositiveHolonomyGaugeExact as Block
import DASHI.Physics.YangMills.YMClaySUNNativeBlockedPositiveHolonomyExact as SUNBlock
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN

-- There are four axis constructors in the original CyclicIndex 4.
-- The unaffected coarse coordinates remain universally quantified.
sideFourTwoBlockEndpoint :
  ∀ {Value : Set}
    (group : Bond.ExactLinkGroup Value) →
  Block.BlockEndpointCompatibility {m = 1} {l = 1} group

sideFourTwoBlockEndpoint group
    (Torus.pair (Torus.pair Torus.zeroᵢ x1)
      (Torus.pair x2 x3)) Torus.zeroᵢ = refl
sideFourTwoBlockEndpoint group
    (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x1)
      (Torus.pair x2 x3)) Torus.zeroᵢ = refl

sideFourTwoBlockEndpoint group
    (Torus.pair (Torus.pair x0 Torus.zeroᵢ)
      (Torus.pair x2 x3)) (Torus.sucᵢ Torus.zeroᵢ) = refl
sideFourTwoBlockEndpoint group
    (Torus.pair (Torus.pair x0 (Torus.sucᵢ Torus.zeroᵢ))
      (Torus.pair x2 x3)) (Torus.sucᵢ Torus.zeroᵢ) = refl

sideFourTwoBlockEndpoint group
    (Torus.pair (Torus.pair x0 x1)
      (Torus.pair Torus.zeroᵢ x3))
    (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl
sideFourTwoBlockEndpoint group
    (Torus.pair (Torus.pair x0 x1)
      (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x3))
    (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl

sideFourTwoBlockEndpoint group
    (Torus.pair (Torus.pair x0 x1)
      (Torus.pair x2 Torus.zeroᵢ))
    (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = refl
sideFourTwoBlockEndpoint group
    (Torus.pair (Torus.pair x0 x1)
      (Torus.pair x2 (Torus.sucᵢ Torus.zeroᵢ)))
    (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = refl

-- The original SUN fields at n=3 are on the literal side-four torus.
-- The blocked fields at n=1 are on the literal side-two torus. Both are
-- the SAME original Variable.SUNPeriodicLinks / Gauge family.
sideFourSUNBlockGaugeCovariant :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (fine : Variable.SUNPeriodicLinks theory 3)
    (gamma : Variable.SUNPeriodicGauge theory 3)
    (coarseBond : Torus.PositiveBond 2) →
  SUNBlock.nativeSUNBlockLinks {m = 1} {l = 1} theory
    (Variable.periodicSUNGaugeTransform theory 3 fine gamma)
    coarseBond
  ≡
  Variable.periodicSUNGaugeTransform theory 1
    (SUNBlock.nativeSUNBlockLinks {m = 1} {l = 1} theory fine)
    (SUNBlock.nativeSUNBlockGauge {m = 1} {l = 1}
      theory gamma)
    coarseBond
sideFourSUNBlockGaugeCovariant theory fine gamma coarseBond =
  SUNBlock.nativeSUNBlockGaugeLawOnCoarse {m = 1} {l = 1}
    theory (sideFourTwoBlockEndpoint
      (Native.sunExactSignedLinkGroup theory))
    fine gamma coarseBond
