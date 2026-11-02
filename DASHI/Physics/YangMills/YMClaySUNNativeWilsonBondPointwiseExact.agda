{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySUNNativeWilsonBondPointwiseExact where

------------------------------------------------------------------------
-- THE ORIGINAL PERIODIC LINK CARRIER IS A FUNCTION TYPE.
-- Its literal Wilson words need only POINTWISE equality of bond links.
-- This provides the required same-object finite-observable extensionality,
-- without postulating arbitrary function extensionality or changing the
-- selected physical lattice into a convenient surrogate Vec carrier.
--
-- Reuses: original signed periodic oriented link and path holonomy,
-- the original SUN matrix group, six-positive-plane real source,
-- prior finite real-sum congruence and physical Wilson/Gibbs definition.
--
-- A general *function equality* in the old SUNNativeBondProductCodec is a
-- distinct proof-theoretic requirement. This module does not claim to
-- inhabit that record or extend Haar to arbitrary functions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 1ℝ; _-ℝ_; _*ℝ_; -ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Signed
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as Gibbs
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGaugeInvariantExact as Gauge
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

NativeBondPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
  Native.SUNSideFourLinks N theory →
  Native.SUNSideFourLinks N theory → Set
NativeBondPointwise theory left right =
  ∀ bond → left bond ≡ right bond

nativeOrientedLinkPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (left right : Native.SUNSideFourLinks N theory) →
    NativeBondPointwise theory left right →
    (site : Hodge.Site4) (direction : Signed.SignedAxis4) →
  Bond.orientedLinkBase
    (Native.sunExactSignedLinkGroup theory) left site direction
  ≡ Bond.orientedLinkBase
      (Native.sunExactSignedLinkGroup theory) right site direction
nativeOrientedLinkPointwise theory left right same site
    (Torus.pair axis true) =
  same (Torus.pair site axis)
nativeOrientedLinkPointwise theory left right same site
    (Torus.pair axis false) =
  cong (SUN.sunInverse theory)
    (same (Torus.pair (Bond.negativeStep site axis) axis))

nativeSignedPathPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (left right : Native.SUNSideFourLinks N theory) →
    NativeBondPointwise theory left right →
    (site : Hodge.Site4) →
    (directions : List Signed.SignedAxis4) →
  Native.sunSignedPathHolonomy theory left site directions
    ≡ Native.sunSignedPathHolonomy theory right site directions
nativeSignedPathPointwise theory left right same site [] = refl
nativeSignedPathPointwise theory left right same site
    (direction ∷ directions) =
  cong₂ (SUN.sunMultiply theory)
    (nativeOrientedLinkPointwise theory left right same site direction)
    (nativeSignedPathPointwise theory left right same
      (Bond.walkStep site direction) directions)

nativeSUNPositivePlaquettePointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (left right : Native.SUNSideFourLinks N theory) →
    NativeBondPointwise theory left right →
    (plaquette : Plaquette.PeriodicPlaquette Weld.three) →
  Native.sunPositivePlaquetteHolonomy theory left plaquette
  ≡ Native.sunPositivePlaquetteHolonomy theory right plaquette
nativeSUNPositivePlaquettePointwise theory left right same plaquette =
  nativeSignedPathPointwise theory left right same
    (Torus.first plaquette)
    (Bond.plaquetteBoundaryDirections (Torus.second plaquette))

nativeSUNSixDeficitPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (left right : Native.SUNSideFourLinks N theory) →
    NativeBondPointwise theory left right →
  Gibbs.nativeSUNSixWilsonDeficit theory traceData left
  ≡ Gibbs.nativeSUNSixWilsonDeficit theory traceData right
nativeSUNSixDeficitPointwise theory traceData left right same =
  Gauge.sumSitesRealCong _ _
    (λ site →
      Sums.realSumCong (Plaquette.ownedPeriodicPlaquettes site)
        (λ plaquette →
          cong (1ℝ -ℝ_)
            (cong (Trace.matrixWilsonValue traceData)
              (nativeSUNPositivePlaquettePointwise
                theory left right same plaquette))))

nativeSUNWilsonActionPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (beta : ℝ)
    (left right : Native.SUNSideFourLinks N theory) →
    NativeBondPointwise theory left right →
  Gibbs.nativeSUNWilsonAction theory traceData beta left
  ≡ Gibbs.nativeSUNWilsonAction theory traceData beta right
nativeSUNWilsonActionPointwise theory traceData beta left right same =
  cong (beta *ℝ_)
    (nativeSUNSixDeficitPointwise theory traceData left right same)

nativeSUNGibbsDensityPointwise :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (left right : Native.SUNSideFourLinks N theory) →
    NativeBondPointwise theory left right →
  Gibbs.nativeSUNWilsonGibbsDensity theory traceData exponential beta left
  ≡ Gibbs.nativeSUNWilsonGibbsDensity theory traceData exponential beta right
nativeSUNGibbsDensityPointwise
    theory traceData exponential beta left right same =
  cong (λ action → Exp.expReal exponential (-ℝ action))
    (nativeSUNWilsonActionPointwise
      theory traceData beta left right same)
