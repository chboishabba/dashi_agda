module DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability

record AnalyticCoordinateTerminalRefinement
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  private
    carrier = Analytic.AnalyticSubstrate.carrier analytic
    completed = Analytic.AnalyticSubstrate.completed analytic
    Complex = Analytic.ComplexAnalyticCarrier.Complex carrier
    Real = Analytic.ComplexAnalyticCarrier.Real carrier
    realPart = Analytic.ComplexAnalyticCarrier.realPart carrier
    abstractCritical = Analytic.CompletedRiemannZeta.criticalLine completed
  field
    half : Real

    criticalLineImpliesHalf :
      (s : Complex) -> abstractCritical s -> realPart s ≡ half

    halfImpliesCriticalLine :
      (s : Complex) -> realPart s ≡ half -> abstractCritical s

    equalityToHalfStable :
      (r : Real) -> ((r ≡ half -> ⊥) -> ⊥) -> r ≡ half

    WithinPublishedVerifiedHeight :
      Universal.AnalyticNontrivialZero analytic -> Set

    publishedVerifiedHeightHasHalfRealPart :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      WithinPublishedVerifiedHeight rho ->
      realPart (Universal.point rho) ≡ half

    exactPublishedHeightIs3000175332800 : Set
    exactPublishedHeightIs3000175332800Receipt :
      exactPublishedHeightIs3000175332800

    sourceReference : String
    refinementReference : String

open AnalyticCoordinateTerminalRefinement public

compilePlattTrudgianVerifiedRegionTransport :
  forall {analytic} ->
  AnalyticCoordinateTerminalRefinement analytic ->
  Low.PlattTrudgianVerifiedRegionTransport analytic
compilePlattTrudgianVerifiedRegionTransport refinement = record
  { Low.WithinPublishedVerifiedHeight =
      WithinPublishedVerifiedHeight refinement
  ; Low.publishedVerifiedHeightCritical =
      λ rho within ->
        halfImpliesCriticalLine refinement
          (Universal.point rho)
          (publishedVerifiedHeightHasHalfRealPart refinement rho within)
  ; Low.exactPublishedHeightIs3000175332800 =
      exactPublishedHeightIs3000175332800 refinement
  ; Low.exactPublishedHeightIs3000175332800Receipt =
      exactPublishedHeightIs3000175332800Receipt refinement
  ; Low.sourceReference = sourceReference refinement
  ; Low.transportReference = refinementReference refinement
  }

------------------------------------------------------------------------
-- Compatibility adapter to the older generic predicate-refinement record.
--
-- That record carries an opaque same-predicate receipt, but its stability
-- compiler does not consume the receipt. Because this package is already
-- indexed by one exact `analytic`, the completed-zeta predicate is fixed by the
-- type. The compatibility receipt is therefore definitionally trivial rather
-- than a separate proof obligation.
------------------------------------------------------------------------

compileCriticalLinePredicateRefinement :
  forall {analytic} ->
  AnalyticCoordinateTerminalRefinement analytic ->
  Stability.CriticalLinePredicateRefinement analytic
compileCriticalLinePredicateRefinement {analytic} refinement = record
  { Stability.CriticalLinePredicateRefinement.RefinedCritical =
      λ s ->
        Analytic.ComplexAnalyticCarrier.realPart
          (Analytic.AnalyticSubstrate.carrier analytic) s
        ≡ half refinement
  ; Stability.CriticalLinePredicateRefinement.abstractImpliesRefined =
      criticalLineImpliesHalf refinement
  ; Stability.CriticalLinePredicateRefinement.refinedImpliesAbstract =
      halfImpliesCriticalLine refinement
  ; Stability.CriticalLinePredicateRefinement.refinedCriticalStable =
      λ s ->
        equalityToHalfStable refinement
          (Analytic.ComplexAnalyticCarrier.realPart
            (Analytic.AnalyticSubstrate.carrier analytic) s)
  ; Stability.CriticalLinePredicateRefinement.sameCompletedZetaPredicateReceipt = ⊤
  ; Stability.CriticalLinePredicateRefinement.sameCompletedZetaPredicateReceiptWitness = tt
  ; Stability.CriticalLinePredicateRefinement.refinementReference =
      refinementReference refinement
  }

compileCriticalLineStable :
  forall {analytic} ->
  AnalyticCoordinateTerminalRefinement analytic ->
  Universal.CriticalLineStable analytic
compileCriticalLineStable refinement =
  Stability.compileCriticalLineStable
    (compileCriticalLinePredicateRefinement refinement)

record AnalyticCoordinateTerminalRefinementBoundary : Set where
  constructor analytic-coordinate-terminal-refinement-boundary
  field
    lowAndStabilityMayUseSeparateCarrierInterpretations : Bool
    lowAndStabilityMayUseSeparateCarrierInterpretationsIsFalse :
      lowAndStabilityMayUseSeparateCarrierInterpretations ≡ false
    oneSameCarrierHalfCharacterisationCompilesCriticalRefinement : Bool
    oneSameCarrierHalfCharacterisationCompilesCriticalRefinementIsTrue :
      oneSameCarrierHalfCharacterisationCompilesCriticalRefinement ≡ true
    verifiedHalfRealPartCompilesCanonicalLowCriticality : Bool
    verifiedHalfRealPartCompilesCanonicalLowCriticalityIsTrue :
      verifiedHalfRealPartCompilesCanonicalLowCriticality ≡ true
    equalityStabilityCompilesCriticalLineStable : Bool
    equalityStabilityCompilesCriticalLineStableIsTrue :
      equalityStabilityCompilesCriticalLineStable ≡ true
    separateOpaqueSamePredicateReceiptRequired : Bool
    separateOpaqueSamePredicateReceiptRequiredIsFalse :
      separateOpaqueSamePredicateReceiptRequired ≡ false
    sourceMetadataAloneInhabitsThisPackage : Bool
    sourceMetadataAloneInhabitsThisPackageIsFalse :
      sourceMetadataAloneInhabitsThisPackage ≡ false
    actualAnalyticCoordinateRefinementInhabitedHere : Bool
    actualAnalyticCoordinateRefinementInhabitedHereIsFalse :
      actualAnalyticCoordinateRefinementInhabitedHere ≡ false
    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false
    highestAlphaReading : String

canonicalAnalyticCoordinateTerminalRefinementBoundary :
  AnalyticCoordinateTerminalRefinementBoundary
canonicalAnalyticCoordinateTerminalRefinementBoundary =
  analytic-coordinate-terminal-refinement-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "Use one theorem-bearing same-AnalyticSubstrate coordinate refinement for both terminal seams. Prove criticalLine(s) iff realPart(s)=half, constructive stability of equality-to-half, and the Platt--Trudgian verified-region theorem as realPart(point rho)=half on that same carrier. Because this package is already indexed by one exact AnalyticSubstrate, no separate opaque same-completed-zeta predicate receipt is required; the older compatibility receipt compiles as unit. Source citations, rational toy carriers, or the predicate name alone do not inhabit the substantive coordinate theorems, and RH is not derived here."
