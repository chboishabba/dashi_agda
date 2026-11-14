module DASHI.Physics.YangMills.YMClayNativeSixPlaquetteSUNWilsonActionWeldExact where

------------------------------------------------------------------------
-- ORIGINAL CANONICAL SUNWilsonAction = ORIGINAL 6-PLANE NATIVE SIGNED ACTION
--
-- Before this bridge, generic SUNWilsonAction already owned the finite
-- SU(N) Wilson action/gauge theorem, while original Bałaban
-- PeriodicBondPathBianchiExact had the literal signed +/- native word and
-- six-positive-plane source geometry. This module connects THOSE OWNERS.
--
-- No second trace authority: the derived trace cyclicity produces an
-- original SUNWilsonClassFunction.SUNWilsonTraceAuthority.
-- No new plaquette convention: the original positive six plane at each
-- original side-four periodic site is the selected SUNWilsonAction list.
--
-- Physical sources: K. Wilson (1974), DOI 10.1103/PhysRevD.10.2445;
-- T. Bałaban (1985), DOI 10.1007/BF01466594. The code-level bridge
-- is DASHI's. Does not construct Haar, UV/IR or a continuum OS Hamiltonian.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_)

import DASHI.Physics.YangMills.CompactLieLatticeGauge as Gauge
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.SUNWilsonAction as Wilson
import DASHI.Physics.YangMills.SUNWilsonClassFunction as OriginalTrace
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Signed
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Closure
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as Gibbs
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGaugeInvariantExact as GaugeAction

-- Dependent signed edge with its ACTUAL original periodic endpoint.
-- This is exactly the +/- native Balaban bond move, not a second graph.
data NativeSignedEdge : Hodge.Site4 → Hodge.Site4 → Set where
  signedEdge : ∀ {site} (direction : Signed.SignedAxis4) →
    NativeSignedEdge site (Bond.walkStep site direction)

signedWordAsPath :
  ∀ site (word : List Signed.SignedAxis4) →
  Gauge.Path NativeSignedEdge site (Bond.walk site word)
signedWordAsPath site [] = Gauge.empty
signedWordAsPath site (direction ∷ rest) =
  signedEdge direction Gauge.▷
    signedWordAsPath (Bond.walkStep site direction) rest

nativePlaquetteAsClosedPath :
  (plaquette : Plaquette.PeriodicPlaquette Weld.three) →
  Gauge.Path NativeSignedEdge (Torus.first plaquette) (Torus.first plaquette)
nativePlaquetteAsClosedPath plaquette =
  subst
    (Gauge.Path NativeSignedEdge (Torus.first plaquette))
    (Closure.literalPlaquetteCloses
      (Torus.first plaquette) (Torus.second plaquette))
    (signedWordAsPath
      (Torus.first plaquette)
      (Bond.plaquetteBoundaryDirections (Torus.second plaquette)))

sunNativeSignedGaugeField :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
    Native.SUNSideFourLinks N theory →
    Gauge.GaugeField {G = SUN.SUNMatrixElement theory} NativeSignedEdge
sunNativeSignedGaugeField theory bonds
    site .(Bond.walkStep site direction) (signedEdge direction) =
  Bond.orientedLinkBase
    (Native.sunExactSignedLinkGroup theory)
    bonds site direction

-- Here the generic path product and original signed source holonomy are
-- actually the SAME oriented-link recursion.
nativeSignedHolonomyIsCanonicalSUN :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (bonds : Native.SUNSideFourLinks N theory)
    site (word : List Signed.SignedAxis4) →
  Gauge.holonomy (SUN.sunMatrixGroup theory)
    (sunNativeSignedGaugeField theory bonds)
    (signedWordAsPath site word)
  ≡ Native.sunSignedPathHolonomy theory bonds site word
nativeSignedHolonomyIsCanonicalSUN theory bonds site [] = refl
nativeSignedHolonomyIsCanonicalSUN theory bonds site (direction ∷ rest) =
  cong
    (SUN.sunMultiply theory
      (Bond.orientedLinkBase (Native.sunExactSignedLinkGroup theory)
        bonds site direction))
    (nativeSignedHolonomyIsCanonicalSUN theory bonds
      (Bond.walkStep site direction) rest)

-- An indexed path transport changes its ENDPOINT INDEX only, never its
-- value under generic holonomy. This is ordinary identity elimination.
holonomyEndpointTransport :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (bonds : Native.SUNSideFourLinks N theory)
    {start finish target : Hodge.Site4}
    (equality : finish ≡ target)
    (path : Gauge.Path NativeSignedEdge start finish) →
  Gauge.holonomy (SUN.sunMatrixGroup theory)
    (sunNativeSignedGaugeField theory bonds)
    (subst (Gauge.Path NativeSignedEdge start) equality path)
  ≡ Gauge.holonomy (SUN.sunMatrixGroup theory)
      (sunNativeSignedGaugeField theory bonds) path
holonomyEndpointTransport theory bonds refl path = refl

nativePositivePlaquetteIsCanonicalSUN :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (bonds : Native.SUNSideFourLinks N theory)
    (plaquette : Plaquette.PeriodicPlaquette Weld.three) →
  Gauge.holonomy (SUN.sunMatrixGroup theory)
    (sunNativeSignedGaugeField theory bonds)
    (nativePlaquetteAsClosedPath plaquette)
  ≡ Native.sunPositivePlaquetteHolonomy theory bonds plaquette
nativePositivePlaquetteIsCanonicalSUN theory bonds plaquette =
  trans
    (holonomyEndpointTransport
      theory bonds
      (Closure.literalPlaquetteCloses
        (Torus.first plaquette) (Torus.second plaquette))
      (signedWordAsPath
        (Torus.first plaquette)
        (Bond.plaquetteBoundaryDirections (Torus.second plaquette))))
    (nativeSignedHolonomyIsCanonicalSUN theory bonds
      (Torus.first plaquette)
      (Bond.plaquetteBoundaryDirections (Torus.second plaquette)))

-- Uses the canonical generic SUNWilsonActionData. Its selected plaquette
-- list is the ORIGINAL six-positive-plane enumeration for a REAL site.
canonicalNativeSiteSUNWilsonData :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (site : Hodge.Site4) →
  Wilson.SUNWilsonActionData {Scalar = ℝ}
    theory NativeSignedEdge
canonicalNativeSiteSUNWilsonData theory traceData site = record
  { Wilson.SUNWilsonActionData.Plaquette =
      Plaquette.PeriodicPlaquette Weld.three
  ; Wilson.SUNWilsonActionData.plaquettes =
      Plaquette.ownedPeriodicPlaquettes site
  ; Wilson.SUNWilsonActionData.plaquetteBase =
      Torus.first
  ; Wilson.SUNWilsonActionData.plaquetteBoundary =
      nativePlaquetteAsClosedPath
  ; Wilson.SUNWilsonActionData.scalarOperations =
      record
        { Wilson.WilsonScalarOperations.zeroS = 0ℝ
        ; Wilson.WilsonScalarOperations.oneS = 1ℝ
        ; Wilson.WilsonScalarOperations.addS = _+ℝ_
        ; Wilson.WilsonScalarOperations.subtractS = _-ℝ_
        }
  ; Wilson.SUNWilsonActionData.traceAuthority =
      Trace.asCanonicalSUNTraceAuthority traceData
  }

-- The canonical generic SU(N) action on ANY selected original plaquette
-- sublist is precisely the original sum of (1-normalized ReTrace)
-- of the native signed-word plaquette. No trace normalization change.
canonicalNativeSUNWilsonSelectedListExact :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (bonds : Native.SUNSideFourLinks N theory)
    (site : Hodge.Site4)
    (selected : List (Plaquette.PeriodicPlaquette Weld.three)) →
  Wilson.sunWilsonActionFrom
    (canonicalNativeSiteSUNWilsonData theory traceData site)
    selected (sunNativeSignedGaugeField theory bonds)
  ≡ Sums.realSum selected
      (λ p → 1ℝ -ℝ Trace.matrixWilsonValue traceData
        (Native.sunPositivePlaquetteHolonomy theory bonds p))
canonicalNativeSUNWilsonSelectedListExact theory traceData bonds site [] =
  refl
canonicalNativeSUNWilsonSelectedListExact theory traceData bonds site (p ∷ ps) =
  cong₂ _+ℝ_
    (cong (1ℝ -ℝ_)
      (nativePositivePlaquetteIsCanonicalSUN theory bonds p))
    (canonicalNativeSUNWilsonSelectedListExact
      theory traceData bonds site ps)

-- Final same-object target: canonical generic SUNWilsonAction is now
-- identified with the already-selected six-plane real Wilson source AT
-- EVERY physical site, not a second unconnected action.
nativeSixAtSiteIsCanonicalSUNWilsonAction :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (bonds : Native.SUNSideFourLinks N theory) (site : Hodge.Site4) →
  Wilson.sunWilsonAction
    (canonicalNativeSiteSUNWilsonData theory traceData site)
    (sunNativeSignedGaugeField theory bonds)
  ≡ Gibbs.nativeSUNSixWilsonDeficitAt theory traceData bonds site
nativeSixAtSiteIsCanonicalSUNWilsonAction theory traceData bonds site =
  canonicalNativeSUNWilsonSelectedListExact theory traceData bonds
    site (Plaquette.ownedPeriodicPlaquettes site)


------------------------------------------------------------------------
-- Exact original global six-plane action = the canonical existing
-- SUNWilsonAction site fold, with the literal 4^4 periodic site sum.
-- This eliminates an independent "generic SUN vs native SUN" action equality
-- at the selected R443/R445 finite source.
------------------------------------------------------------------------

canonicalSUNSixWilsonDeficit :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory) →
  Native.SUNSideFourLinks N theory → ℝ
canonicalSUNSixWilsonDeficit theory traceData bonds =
  Gibbs.sumSitesReal
    (λ site →
      Wilson.sunWilsonAction
        (canonicalNativeSiteSUNWilsonData theory traceData site)
        (sunNativeSignedGaugeField theory bonds))

nativeSixGlobalIsCanonicalSUNWilsonAction :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (bonds : Native.SUNSideFourLinks N theory) →
  canonicalSUNSixWilsonDeficit theory traceData bonds
  ≡ Gibbs.nativeSUNSixWilsonDeficit theory traceData bonds
nativeSixGlobalIsCanonicalSUNWilsonAction theory traceData bonds =
  GaugeAction.sumSitesRealCong _ _
    (nativeSixAtSiteIsCanonicalSUNWilsonAction theory traceData bonds)

nativeSUNBetaActionIsCanonicalWilsonAction :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (beta : ℝ) (bonds : Native.SUNSideFourLinks N theory) →
  beta *ℝ canonicalSUNSixWilsonDeficit theory traceData bonds
  ≡ Gibbs.nativeSUNWilsonAction theory traceData beta bonds
nativeSUNBetaActionIsCanonicalWilsonAction theory traceData beta bonds =
  cong (beta *ℝ_)
    (nativeSixGlobalIsCanonicalSUNWilsonAction theory traceData bonds)
