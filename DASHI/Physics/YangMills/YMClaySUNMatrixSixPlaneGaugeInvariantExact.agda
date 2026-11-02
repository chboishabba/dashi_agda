module DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGaugeInvariantExact where

------------------------------------------------------------------------
-- R443: FULL SIX-POSITIVE-PLANE SUN MATRIX GIBBS GAUGE INVARIANCE
--
-- Previous theorem owners:
--   BalabanClayGate4PeriodicBondPathBianchiExact: exact signed plaquettes,
--     transformed links and local gauge telescoping;
--   YMClaySUNMatrixWilsonTraceGaugeExact: trace-cyclicity -> conjugation
--     invariance for native SU(N) matrix Wilson loops;
--   YMClaySUNMatrixSixPlaneGibbsDensityExact: physical six-positive-plane
--     real action and selected exp(-beta*S) finite Gibbs density.
--
-- New DASHI contribution: prove the whole selected Wilson action and Gibbs
-- density are invariant under the SAME native local site gauge, not merely
-- an unrelated selected group action. The proof passes the existing local
-- plaquette gauge cancellation through the actual six-term real sum and
-- actual 4^4-site sum. Does not add new Haar, continuum or spectral axioms.
--
-- Attribution: K. Wilson, Phys. Rev. D 10 (1974) 2445-2459,
-- DOI 10.1103/PhysRevD.10.2445; T. Balaban, CMP 99 (1985) 75-102,
-- DOI 10.1007/BF01466594. Pre-existing DASHI proof owners retained.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; -ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as Gibbs
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

-- Physical gauge action is the native original transformedBond (positive
-- link prescription gamma_x U_{xy} gamma_y^{-1}). It is *not* a second
-- invented gauge action on the real source.
sunGaugeTransformedBonds :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (links : Native.SUNSideFourLinks N theory)
    (gamma : Bond.PeriodicSiteGauge Weld.three (SUN.SUNMatrixElement theory)) →
  Native.SUNSideFourLinks N theory
sunGaugeTransformedBonds theory links gamma =
  Bond.transformedBond (Trace.sunGaugeRealization theory links gamma)

-- Both native path recursions evaluate precisely the same signed
-- transformed link at each step; the original orientedLinkBase uses
-- the transformed positive bond and its inverse for negative directions.
sunTransformedPathSameSource :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (links : Native.SUNSideFourLinks N theory)
    (gamma : Bond.PeriodicSiteGauge Weld.three (SUN.SUNMatrixElement theory))
    site word →
  Native.sunSignedPathHolonomy theory
    (sunGaugeTransformedBonds theory links gamma) site word
  ≡ Bond.transformedPathHolonomy
      (Trace.sunGaugeRealization theory links gamma) site word
sunTransformedPathSameSource theory links gamma site word = refl

sunPlaquetteRealTraceGaugeInvariant :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = Scalar} theory)
    (links : Native.SUNSideFourLinks N theory)
    (gamma : Bond.PeriodicSiteGauge Weld.three (SUN.SUNMatrixElement theory))
    (plaquette : Plaquette.PeriodicPlaquette Weld.three) →
  Trace.matrixWilsonValue traceData
    (Native.sunPositivePlaquetteHolonomy theory
      (sunGaugeTransformedBonds theory links gamma) plaquette)
  ≡ Trace.matrixWilsonValue traceData
    (Native.sunPositivePlaquetteHolonomy theory links plaquette)
sunPlaquetteRealTraceGaugeInvariant theory traceData links gamma plaquette =
  trans
    (cong (Trace.matrixWilsonValue traceData)
      (sunTransformedPathSameSource theory links gamma
        (Torus.first plaquette)
        (Bond.plaquetteBoundaryDirections (Torus.second plaquette))))
    (Trace.sunOriginalPlaquetteTraceGaugeInvariant
      theory traceData links gamma plaquette)

-- Explicit congruence on the existing four-index real site-sum. These
-- steps need no new order or Fubini analysis; this is a finite expression.
sumFourRealCong :
  ∀ (left right : Hodge.Index4 → ℝ) →
  (∀ index → left index ≡ right index) →
  Gibbs.sumFourReal left ≡ Gibbs.sumFourReal right
sumFourRealCong left right pointwise
  rewrite pointwise Hodge.index0
        | pointwise Hodge.index1
        | pointwise Hodge.index2
        | pointwise Hodge.index3 = refl

sumSitesRealCong :
  ∀ (left right : Hodge.Site4 → ℝ) →
  (∀ site → left site ≡ right site) →
  Gibbs.sumSitesReal left ≡ Gibbs.sumSitesReal right
sumSitesRealCong left right pointwise =
  sumFourRealCong _ _ (λ x0 →
    sumFourRealCong _ _ (λ x1 →
      sumFourRealCong _ _ (λ x2 →
        sumFourRealCong _ _ (λ x3 →
          pointwise
            (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))))))

sunSixDeficitAtGaugeInvariant :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (links : Native.SUNSideFourLinks N theory)
    (gamma : Bond.PeriodicSiteGauge Weld.three (SUN.SUNMatrixElement theory))
    site →
  Gibbs.nativeSUNSixWilsonDeficitAt theory traceData
    (sunGaugeTransformedBonds theory links gamma) site
  ≡ Gibbs.nativeSUNSixWilsonDeficitAt theory traceData links site
sunSixDeficitAtGaugeInvariant theory traceData links gamma site =
  Sums.realSumCong (Plaquette.ownedPeriodicPlaquettes site)
    (λ p → cong (1ℝ -ℝ_)
      (sunPlaquetteRealTraceGaugeInvariant theory traceData links gamma p))

sunSixDeficitGaugeInvariant :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (links : Native.SUNSideFourLinks N theory)
    (gamma : Bond.PeriodicSiteGauge Weld.three (SUN.SUNMatrixElement theory)) →
  Gibbs.nativeSUNSixWilsonDeficit theory traceData
    (sunGaugeTransformedBonds theory links gamma)
  ≡ Gibbs.nativeSUNSixWilsonDeficit theory traceData links
sunSixDeficitGaugeInvariant theory traceData links gamma =
  sumSitesRealCong _ _
    (sunSixDeficitAtGaugeInvariant theory traceData links gamma)

sunWilsonActionGaugeInvariant :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (beta : ℝ)
    (links : Native.SUNSideFourLinks N theory)
    (gamma : Bond.PeriodicSiteGauge Weld.three (SUN.SUNMatrixElement theory)) →
  Gibbs.nativeSUNWilsonAction theory traceData beta
    (sunGaugeTransformedBonds theory links gamma)
  ≡ Gibbs.nativeSUNWilsonAction theory traceData beta links
sunWilsonActionGaugeInvariant theory traceData beta links gamma =
  cong (beta *ℝ_)
    (sunSixDeficitGaugeInvariant theory traceData links gamma)

sunGibbsDensityGaugeInvariant :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (links : Native.SUNSideFourLinks N theory)
    (gamma : Bond.PeriodicSiteGauge Weld.three (SUN.SUNMatrixElement theory)) →
  Gibbs.nativeSUNWilsonGibbsDensity theory traceData exponential beta
    (sunGaugeTransformedBonds theory links gamma)
  ≡ Gibbs.nativeSUNWilsonGibbsDensity theory traceData exponential beta links
sunGibbsDensityGaugeInvariant theory traceData exponential beta links gamma =
  cong (λ action → Exp.expReal exponential (-ℝ action))
    (sunWilsonActionGaugeInvariant theory traceData beta links gamma)
