module DASHI.Foundations.WetteTranslatedBernaysObstructionExact where

------------------------------------------------------------------------
-- BERNAYS REDUCTION + PROOF TRANSLATION
--
-- A central audit question for Wette is not merely whether his internal
-- calculus derives a designated contradiction, but whether that derivation is
-- transported by a justified interpretation into the comparison arithmetic.
--
-- This module composes two already-separated owners:
--
--   finite proof of Wette-Con
--     -> finite Wette contradiction          (Bernays-style reduction)
--     -> finite target contradiction         (proof translation)
--
-- No semantic reflection is inserted.  Therefore even the final target proof
-- remains a proof-theoretic derivability statement until a soundness/reflection
-- bridge is separately supplied.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.WetteConstructiveAutomatonExact as W
import DASHI.Foundations.WetteFiniteDeductionTraceExact as Trace
import DASHI.Foundations.WetteFiniteDerivabilityBernaysBridgeExact as BernaysTrace
import DASHI.Foundations.WetteFiniteCalculusTranslationExact as Translation

------------------------------------------------------------------------
-- Push a Bernays-generated source contradiction through a separately supplied
-- contradiction-preserving translation.
------------------------------------------------------------------------

finiteConsistencyTraceYieldsTranslatedContradiction :
  {sourceMachine targetMachine : W.WetteMachineSpec} →
  {source : W.WetteDeductionSimulation sourceMachine} →
  {target : W.WetteDeductionSimulation targetMachine} →
  (bridge : Translation.ContradictionPreservingTranslation source target) →
  (consistencySentence : W.Syntax source) →
  (reduction :
    Trace.FiniteDerivationWitness source
      (Translation.sourceBase bridge) consistencySentence →
    Trace.FiniteDerivationWitness source
      (Translation.sourceBase bridge)
      (Translation.sourceContradiction bridge)) →
  Trace.FiniteDerivationWitness source
    (Translation.sourceBase bridge) consistencySentence →
  Trace.FiniteDerivationWitness target
    (Translation.targetBase bridge)
    (Translation.targetContradiction bridge)
finiteConsistencyTraceYieldsTranslatedContradiction
  {source = source} bridge consistencySentence reduction proof =
  Translation.sourceContradictionDerivationTransfers bridge
    (BernaysTrace.finiteConsistencyTraceYieldsContradictionTrace
      source
      (Translation.sourceBase bridge)
      consistencySentence
      (Translation.sourceContradiction bridge)
      reduction
      proof)

------------------------------------------------------------------------
-- A consistency result for the target calculus can therefore obstruct an
-- internal Wette consistency proof, but only after both the Bernays reduction
-- and the contradiction-preserving translation have been provided.
------------------------------------------------------------------------

targetFiniteConsistencyBlocksSourceConsistencyTrace :
  {sourceMachine targetMachine : W.WetteMachineSpec} →
  {source : W.WetteDeductionSimulation sourceMachine} →
  {target : W.WetteDeductionSimulation targetMachine} →
  (bridge : Translation.ContradictionPreservingTranslation source target) →
  (consistencySentence : W.Syntax source) →
  (reduction :
    Trace.FiniteDerivationWitness source
      (Translation.sourceBase bridge) consistencySentence →
    Trace.FiniteDerivationWitness source
      (Translation.sourceBase bridge)
      (Translation.sourceContradiction bridge)) →
  Translation.FiniteConsistent target
    (Translation.targetBase bridge)
    (Translation.targetContradiction bridge) →
  ¬ Trace.FiniteDerivationWitness source
      (Translation.sourceBase bridge) consistencySentence
targetFiniteConsistencyBlocksSourceConsistencyTrace
  bridge consistencySentence reduction targetConsistent proof =
  targetConsistent
    (finiteConsistencyTraceYieldsTranslatedContradiction
      bridge consistencySentence reduction proof)

------------------------------------------------------------------------
-- Conversely, a source contradiction can be transported without having any
-- internal-consistency proof at all.  This keeps contradiction transport and
-- the special Bernays/Wette Con-to-bottom reduction logically separate.
------------------------------------------------------------------------

sourceContradictionTransfersIndependently :
  {sourceMachine targetMachine : W.WetteMachineSpec} →
  {source : W.WetteDeductionSimulation sourceMachine} →
  {target : W.WetteDeductionSimulation targetMachine} →
  (bridge : Translation.ContradictionPreservingTranslation source target) →
  Trace.FiniteDerivationWitness source
    (Translation.sourceBase bridge)
    (Translation.sourceContradiction bridge) →
  Trace.FiniteDerivationWitness target
    (Translation.targetBase bridge)
    (Translation.targetContradiction bridge)
sourceContradictionTransfersIndependently =
  Translation.sourceContradictionDerivationTransfers

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record WetteTranslatedBernaysBoundary : Set where
  constructor wetteTranslatedBernaysBoundary
  field
    bernaysReductionAndTranslationCompose : Bool
    bernaysReductionAndTranslationComposeIsTrue :
      bernaysReductionAndTranslationCompose ≡ true

    targetConsistencyCanBlockSourceConProofGivenBothBridges : Bool
    targetConsistencyCanBlockSourceConProofGivenBothBridgesIsTrue :
      targetConsistencyCanBlockSourceConProofGivenBothBridges ≡ true

    contradictionTransportRequiresInternalConsistencyProof : Bool
    contradictionTransportRequiresInternalConsistencyProofIsFalse :
      contradictionTransportRequiresInternalConsistencyProof ≡ false

    translatedContradictionProofIsAlreadySemanticAbsurdity : Bool
    translatedContradictionProofIsAlreadySemanticAbsurdityIsFalse :
      translatedContradictionProofIsAlreadySemanticAbsurdity ≡ false

    historicalWetteComparisonArithmeticBridgeRecovered : Bool
    historicalWetteComparisonArithmeticBridgeRecoveredIsFalse :
      historicalWetteComparisonArithmeticBridgeRecovered ≡ false

canonicalWetteTranslatedBernaysBoundary : WetteTranslatedBernaysBoundary
canonicalWetteTranslatedBernaysBoundary =
  wetteTranslatedBernaysBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
