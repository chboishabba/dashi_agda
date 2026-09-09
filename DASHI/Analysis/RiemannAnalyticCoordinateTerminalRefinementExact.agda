module DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability

------------------------------------------------------------------------
-- SHARED SAME-CARRIER TERMINAL COORDINATE REFINEMENT
--
-- The low verified-region theorem and the final double-negation stability seam
-- should not each invent their own interpretation of the analytic carrier.
-- Use one exact coordinate package on the SAME AnalyticSubstrate:
--
--   criticalLine(s) <-> realPart(s) = half,
--
-- together with constructive stability of equality-to-half and the published
-- verified-region theorem expressed on that same coordinate.  From this single
-- package we compile both the canonical Platt--Trudgian low transport and the
-- CriticalLinePredicateRefinement used by the positive-RH compiler.
--
-- The package is theorem-bearing.  Source metadata alone cannot construct it.
------------------------------------------------------------------------

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
      (s : Complex) ->
      abstractCritical s ->
      realPart s ≡ half

    halfImpliesCriticalLine :
      (s : Complex) ->
      realPart s ≡ half ->
      abstractCritical s

    equalityToHalfStable :
      (r : Real) ->
      ((r ≡ half -> ⊥) -> ⊥) ->
      r ≡ half

    WithinPublishedVerifiedHeight :
      Universal.AnalyticNontrivialZero analytic -> Set

    publishedVerifiedHeightHasHalfRealPart :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      WithinPublishedVerifiedHeight rho ->
      realPart (Universal.point rho) ≡ half

    exactPublishedHeightIs3000175332800 : Set
    exactPublishedHeightIs3000175332800Receipt :
      exactPublishedHeightIs3000175332800

    sameCompletedZetaPredicateReceipt : Set
    sameCompletedZetaPredicateReceiptWitness :
      sameCompletedZetaPredicateReceipt

    sourceReference : String
    refinementReference : String

open AnalyticCoordinateTerminalRefinement public

------------------------------------------------------------------------
-- Shared coordinate -> canonical low transport.
------------------------------------------------------------------------

compilePlattTrudgianVerifiedRegionTransport :
  forall {analytic} ->
  AnalyticCoordinateTerminalRefinement analytic ->
  Low.PlattTrudgianVerifiedRegionTransport analytic
compilePlattTrudgianVerifiedRegionTransport refinement = record
  { Low.WithinPublishedVerifiedHeight =
      WithinPublishedVerifiedHeight refinement
  ; Low.publishedVerifiedHeightCritical =
      lambda rho within ->
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
-- Shared coordinate -> exact critical-line predicate refinement/stability.
------------------------------------------------------------------------

compileCriticalLinePredicateRefinement :
  forall {analytic} ->
  AnalyticCoordinateTerminalRefinement analytic ->
  Stability.CriticalLinePredicateRefinement analytic
compileCriticalLinePredicateRefinement {analytic} refinement = record
  { Stability.CriticalLinePredicateRefinement.RefinedCritical =
      lambda s ->
        Analytic.ComplexAnalyticCarrier.realPart
          (Analytic.AnalyticSubstrate.carrier analytic) s
        ≡ half refinement
  ; Stability.CriticalLinePredicateRefinement.abstractImpliesRefined =
      criticalLineImpliesHalf refinement
  ; Stability.CriticalLinePredicateRefinement.refinedImpliesAbstract =
      halfImpliesCriticalLine refinement
  ; Stability.CriticalLinePredicateRefinement.refinedCriticalStable =
      lambda s ->
        equalityToHalfStable refinement
          (Analytic.ComplexAnalyticCarrier.realPart
            (Analytic.AnalyticSubstrate.carrier analytic) s)
  ; Stability.CriticalLinePredicateRefinement.sameCompletedZetaPredicateReceipt =
      sameCompletedZetaPredicateReceipt refinement
  ; Stability.CriticalLinePredicateRefinement.sameCompletedZetaPredicateReceiptWitness =
      sameCompletedZetaPredicateReceiptWitness refinement
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

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

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
    "Use one theorem-bearing same-AnalyticSubstrate coordinate refinement for both terminal seams. Prove criticalLine(s) iff realPart(s)=half, constructive stability of equality-to-half, and the Platt--Trudgian verified-region theorem as realPart(point rho)=half on that same carrier. Those compile the canonical low transport and CriticalLineStable. Source citations, rational toy carriers, or whole-carrier identity alone do not inhabit this package, and RH is not derived here."
