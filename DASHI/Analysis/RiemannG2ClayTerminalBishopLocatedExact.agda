module DASHI.Analysis.RiemannG2ClayTerminalBishopLocatedExact where

------------------------------------------------------------------------
-- PREFERRED CONCRETE LOW-SIDE CLAY TERMINAL
--
-- This route no longer uses:
--   * Agda propositional equality as real equality,
--   * Dec(V),
--   * a full ConstructiveCompleteRealPackage,
--   * an arbitrary low/high cover.
--
-- It uses:
--   * one whole selected-carrier = Bishop-complex same-object weld,
--   * the concrete Bishop located height split,
--   * same-substrate PT low criticality,
--   * criticalLine iff Bishop realPart ~= 1/2,
--   * constructive stability of Bishop setoid equality,
--   * an implementation-neutral uniform high contradiction producer.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₂)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BishopComplex
import DASHI.Analysis.RiemannBishopAnalyticLocatedHeightAttachmentExact as BishopAttachment
import DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact as Located
import DASHI.Analysis.RiemannAnalyticLocatedLowCriticalityCompilerExact as LowCritical
import DASHI.Analysis.RiemannLocatedLowTransportExact as LowTransport
import DASHI.Analysis.RiemannBishopSetoidCriticalLineRefinementExact as BishopCritical
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability
import DASHI.Analysis.RiemannG2UniformHighContradictionExact as High
import DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact as Negative

record ClayTerminalBishopLocatedInput
    (analytic : Analytic.AnalyticSubstrate) : Set₂ where
  field
    functions :
      BishopComplex.BishopComplexAnalyticFunctionLayer

    carrier :
      BishopComplex.CanonicalBishopComplexCarrierRealization
        analytic functions

    lowCriticality :
      LowCritical.PublishedLocatedLowCriticality
        (BishopAttachment.toBishopLocatedHeightAttachment carrier)

    criticalLineCharacterization :
      BishopCritical.BishopCriticalLineHalfCharacterization
        analytic
        (BishopAttachment.toBishopLocatedHeightAttachment carrier)

    highProducer :
      High.UniformHighContradictionProducer
        analytic
        (Located.LocatedHighRegion
          (BishopAttachment.toBishopLocatedHeightAttachment carrier))

    terminalReference : String

open ClayTerminalBishopLocatedInput public

compileBishopLocatedNegativeInput :
  ∀ {analytic} →
  ClayTerminalBishopLocatedInput analytic →
  Negative.GenericHighNegativeRHInput analytic
compileBishopLocatedNegativeInput input = record
  { Negative.genericLowTransport =
      LowTransport.compileLocatedLowTransport
        (lowCriticality input)
  ; Negative.GenericHighRegion =
      Located.LocatedHighRegion
        (BishopAttachment.toBishopLocatedHeightAttachment
          (carrier input))
  ; Negative.genericVerifiedOrHighCover =
      Located.locatedVerifiedOrHigh
        (BishopAttachment.toBishopLocatedHeightAttachment
          (carrier input))
  ; Negative.genericHighProducer =
      highProducer input
  ; Negative.genericCompletionReference =
      terminalReference input
  }

compiledBishopLocatedDoubleNegatedRH :
  ∀ {analytic} →
  ClayTerminalBishopLocatedInput analytic →
  Negative.DoubleNegatedRiemannHypothesisFor analytic
compiledBishopLocatedDoubleNegatedRH input =
  Negative.compileGenericHighNegativeRH
    (compileBishopLocatedNegativeInput input)

compiledBishopCriticalLineRefinement :
  ∀ {analytic} →
  (input : ClayTerminalBishopLocatedInput analytic) →
  Stability.CriticalLinePredicateRefinement analytic
compiledBishopCriticalLineRefinement input =
  BishopCritical.compileBishopCriticalLinePredicateRefinement
    (criticalLineCharacterization input)

compileClayTerminalBishopLocatedToRH :
  ∀ {analytic} →
  ClayTerminalBishopLocatedInput analytic →
  Analytic.RiemannHypothesisFor analytic
compileClayTerminalBishopLocatedToRH input =
  Negative.negativeRHPlusPredicateRefinementImpliesRH
    (compiledBishopCriticalLineRefinement input)
    (compiledBishopLocatedDoubleNegatedRH input)

record ClayTerminalBishopLocatedBoundary : Set where
  constructor clay-terminal-bishop-located-boundary
  field
    agdaRealEqualityRequired : Bool
    exactVerifiedRegionDecisionRequired : Bool
    fullConstructiveRealPackageRequired : Bool
    arbitraryCoverRequired : Bool
    concreteBishopHeightSplitOwned : Bool
    bishopEqualityStabilityOwned : Bool
    wholeCarrierSameObjectWeldStillRequired : Bool
    sameSubstratePTCriticalityStillRequired : Bool
    criticalLineBishopHalfCharacterizationStillRequired : Bool
    implementationNeutralHighProducerStillRequired : Bool
    theseInputsCompileRH : Bool
    inputsInhabitedHere : Bool
    rhDerivedHere : Bool

open ClayTerminalBishopLocatedBoundary public

canonicalClayTerminalBishopLocatedBoundary :
  ClayTerminalBishopLocatedBoundary
canonicalClayTerminalBishopLocatedBoundary =
  clay-terminal-bishop-located-boundary
    false false false false true true
    true true true true true false false
