module DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.DeBruijnNewman2026SourceWeldExact as Source

------------------------------------------------------------------------
-- CANONICAL LOW REGION = THE VERIFIED REGION
--
-- The older low adapter allowed callers to choose an arbitrary `Low` predicate
-- and then separately prove `Low -> WithinPublishedVerifiedHeight`.  That is a
-- useful compatibility interface but not the least-privilege terminal route.
--
-- Normalize the low partition definitionally to the exact verified-region
-- predicate.  The theorem-bearing transport already lands directly in
-- `analyticCritical`, so same-completed-zeta identity is carried by the type of
-- the theorem rather than by an unrelated opaque Set receipt.
------------------------------------------------------------------------

publishedVerifiedHeight : Nat
publishedVerifiedHeight = Source.plattTrudgianVerifiedHeight

record PlattTrudgianVerifiedRegionTransport
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    WithinPublishedVerifiedHeight :
      Universal.AnalyticNontrivialZero analytic -> Set

    publishedVerifiedHeightCritical :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      WithinPublishedVerifiedHeight rho ->
      Universal.analyticCritical rho

    exactPublishedHeightIs3000175332800 : Set
    exactPublishedHeightIs3000175332800Receipt :
      exactPublishedHeightIs3000175332800

    sourceReference : String
    transportReference : String

open PlattTrudgianVerifiedRegionTransport public

CanonicalLowRegion :
  forall {analytic} ->
  PlattTrudgianVerifiedRegionTransport analytic ->
  Universal.AnalyticNontrivialZero analytic -> Set
CanonicalLowRegion transport = WithinPublishedVerifiedHeight transport

canonicalLowCritical :
  forall {analytic} ->
  (transport : PlattTrudgianVerifiedRegionTransport analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  CanonicalLowRegion transport rho ->
  Universal.analyticCritical rho
canonicalLowCritical transport = publishedVerifiedHeightCritical transport

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record CanonicalLowRegionBoundary : Set where
  constructor canonical-low-region-boundary
  field
    arbitraryLowPredicatePrimitiveOnCanonicalRoute : Bool
    arbitraryLowPredicatePrimitiveOnCanonicalRouteIsFalse :
      arbitraryLowPredicatePrimitiveOnCanonicalRoute ≡ false

    separateLowSubsetVerifiedRegionProofRequired : Bool
    separateLowSubsetVerifiedRegionProofRequiredIsFalse :
      separateLowSubsetVerifiedRegionProofRequired ≡ false

    exactSameCarrierCriticalityTheoremStillRequired : Bool
    exactSameCarrierCriticalityTheoremStillRequiredIsTrue :
      exactSameCarrierCriticalityTheoremStillRequired ≡ true

    numericHeightAutomaticallyOrdersAbstractAnalyticReal : Bool
    numericHeightAutomaticallyOrdersAbstractAnalyticRealIsFalse :
      numericHeightAutomaticallyOrdersAbstractAnalyticReal ≡ false

    globalVerifiedRegionOrHighCoverStillRequired : Bool
    globalVerifiedRegionOrHighCoverStillRequiredIsTrue :
      globalVerifiedRegionOrHighCoverStillRequired ≡ true

    canonicalLowCriticalityIsCompilerOutput : Bool
    canonicalLowCriticalityIsCompilerOutputIsTrue :
      canonicalLowCriticalityIsCompilerOutput ≡ true

    exactTransportInhabitedHere : Bool
    exactTransportInhabitedHereIsFalse :
      exactTransportInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalLowRegionBoundary : CanonicalLowRegionBoundary
canonicalLowRegionBoundary =
  canonical-low-region-boundary
    false refl
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "Choose Low definitionally as the Platt--Trudgian verified region on the exact AnalyticSubstrate zero carrier. This removes the separate arbitrary-Low containment theorem and the opaque same-completed-zeta metadata receipt from the canonical path. The substantive low theorem is exactly a proof that every zero in that verified-region predicate is analyticCritical on this same completed-zeta carrier. Because AnalyticSubstrate.Real is abstract, the published numeric height still needs an exact theorem-bearing carrier interpretation. The global verified-region-or-High cover remains independent. RH is not derived here."
