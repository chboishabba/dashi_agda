{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySUNMatrixSpatialC3RealFubiniExact where

------------------------------------------------------------------------
-- ORIGINAL REAL SU(N) SIX-PLANE SPATIAL C3: THE FINITE SITE-SUM PAYMENT.
--
-- Reuse the already existing finite Fubini theorem over *any* additive
-- commutative monoid (BalabanClayGate4FiniteWeightedAdjointFubiniExact).
-- No new real ring solver or matrix/Haar theorem is needed. Two sum-swaps
-- transport the actual 4^4-site Wilson sum along the literal fixed-time
-- spatial C3 permutation (x0,x1,x2,x3) -> (x0,x3,x1,x2).
--
-- The ONLY remaining six-plane C3 physics input is the LOCAL on-source
-- transformed plaquette deficit identity at each site. A full summed
-- action invariance is not assumed or provided separately. SU(N)
-- trace inversion / ordered-plane geometry must supply that local input.
--
-- Original source geometry: Wilson (1974), Balaban (1985). Original
-- generic finite Fubini and site enumeration remain DASHI theorem owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _*ℝ_; +-assoc; +-comm; +-identityˡ; +-identityʳ)

import DASHI.Physics.YangMills.BalabanClayGate4FiniteWeightedAdjointFubiniExact as Sum
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceExact as C3
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as Gibbs
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGaugeInvariantExact as Gauge
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN

realAdditiveMonoid : Sum.AdditiveCommutativeMonoid ℝ
realAdditiveMonoid = record
  { Sum.AdditiveCommutativeMonoid.zero = 0ℝ
  ; Sum.AdditiveCommutativeMonoid.add = _+ℝ_
  ; Sum.AdditiveCommutativeMonoid.addAssociative = +-assoc
  ; Sum.AdditiveCommutativeMonoid.addCommutative = +-comm
  ; Sum.AdditiveCommutativeMonoid.addIdentityLeft = +-identityˡ
  ; Sum.AdditiveCommutativeMonoid.addIdentityRight = +-identityʳ
  }

allFourIndices : List Hodge.Index4
allFourIndices =
  Hodge.index0 ∷ Hodge.index1 ∷ Hodge.index2 ∷ Hodge.index3 ∷ []

-- This is precisely the old native real sum; not a parallel observable.
sumFourRealIsExistingFiniteSum : ∀ (term : Hodge.Index4 → ℝ) →
  Gibbs.sumFourReal term
  ≡ Sum.sumList realAdditiveMonoid allFourIndices term
sumFourRealIsExistingFiniteSum term = refl

realSumFourSwap :
  ∀ (term : Hodge.Index4 → Hodge.Index4 → ℝ) →
  Gibbs.sumFourReal (λ x → Gibbs.sumFourReal (term x))
  ≡ Gibbs.sumFourReal
      (λ y → Gibbs.sumFourReal (λ x → term x y))
realSumFourSwap term =
  Sum.finiteFubini realAdditiveMonoid
    allFourIndices allFourIndices term

-- 2 finite Fubini steps, with original site order and original C3 map.
-- In particular this is NOT the rational Hodge.sumSites theorem transported
-- by a rational-to-real embedding; the summand has native real matrix trace.
realSumSitesSpatialC3 :
  ∀ (term : Hodge.Site4 → ℝ) →
  Gibbs.sumSitesReal (λ site → term (C3.spatialC3Site site))
  ≡ Gibbs.sumSitesReal term
realSumSitesSpatialC3 term =
  Gauge.sumFourRealCong _ _ (λ x0 →
    trans
      (Gauge.sumFourRealCong _ _ (λ x1 →
        realSumFourSwap (λ x2 x3 →
          term (Torus.pair (Torus.pair x0 x3)
                           (Torus.pair x1 x2)))))
      (realSumFourSwap (λ x1 x3 →
        Gibbs.sumFourReal (λ x2 →
          term (Torus.pair (Torus.pair x0 x3)
                           (Torus.pair x1 x2))))))

-- The actual native R443 Wilson six-positive-plane local identity is the
-- ONLY missing C3 source hypothesis in this summation transport. Matrix
-- trace inversion is required only to construct this *local* equality.
nativeSUNSixDeficitC3FromLocal :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (links : Native.SUNSideFourLinks N theory) →
  (∀ site →
    Gibbs.nativeSUNSixWilsonDeficitAt theory traceData
      (Weld.nativeForwardC3Bonds links) site
    ≡ Gibbs.nativeSUNSixWilsonDeficitAt theory traceData
        links (C3.spatialC3Site site)) →
  Gibbs.nativeSUNSixWilsonDeficit theory traceData
    (Weld.nativeForwardC3Bonds links)
  ≡ Gibbs.nativeSUNSixWilsonDeficit theory traceData links
nativeSUNSixDeficitC3FromLocal theory traceData links local =
  trans
    (Gauge.sumSitesRealCong _ _
      local)
    (realSumSitesSpatialC3
      (Gibbs.nativeSUNSixWilsonDeficitAt theory traceData links))

nativeSUNWilsonActionC3FromLocal :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (beta : ℝ)
    (links : Native.SUNSideFourLinks N theory) →
  (∀ site →
    Gibbs.nativeSUNSixWilsonDeficitAt theory traceData
      (Weld.nativeForwardC3Bonds links) site
    ≡ Gibbs.nativeSUNSixWilsonDeficitAt theory traceData
        links (C3.spatialC3Site site)) →
  Gibbs.nativeSUNWilsonAction theory traceData beta
      (Weld.nativeForwardC3Bonds links)
  ≡ Gibbs.nativeSUNWilsonAction theory traceData beta links
nativeSUNWilsonActionC3FromLocal theory traceData beta links local =
  cong (beta *ℝ_)
    (nativeSUNSixDeficitC3FromLocal theory traceData links local)
