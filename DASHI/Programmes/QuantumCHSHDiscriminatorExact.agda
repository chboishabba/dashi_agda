module DASHI.Programmes.QuantumCHSHDiscriminatorExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact as Physical

------------------------------------------------------------------------
-- Concrete dashiQ qubit calibration surface.
--
-- `computer_v2.py` already exposes a CHSH observable and uses the declared
-- classical threshold |S| > 2 as its qubit runtime discriminator.  This module
-- formalises only the discrete prediction-language consequence of that split;
-- it does not formalise floating point arithmetic, sampling statistics, Bell's
-- theorem, or a quantum-gravity theory.
------------------------------------------------------------------------

data CHSHExperiment : Set where
  chsh : CHSHExperiment

data CHSHCandidate : Set where
  classicalBounded : CHSHCandidate
  violationPermitting : CHSHCandidate

data CHSHOutcome : Set where
  withinClassicalBound : CHSHOutcome
  violatesClassicalBound : CHSHOutcome

chshLanguage : Physical.Language CHSHExperiment
chshLanguage chsh = ⊤

chshPredictions :
  Physical.Predictions CHSHCandidate CHSHExperiment CHSHOutcome
chshPredictions classicalBounded chsh withinClassicalBound = ⊤
chshPredictions classicalBounded chsh violatesClassicalBound = ⊥
chshPredictions violationPermitting chsh withinClassicalBound = ⊤
chshPredictions violationPermitting chsh violatesClassicalBound = ⊤

chshViolationDiscriminatesCandidateClasses :
  Physical.Discriminates
    chshPredictions
    chsh
    classicalBounded
    violationPermitting
chshViolationDiscriminatesCandidateClasses =
  violatesClassicalBound , inj₂ (tt , (λ ()))

chshViolationRefutesCandidateEquivalence :
  ¬ (Physical.EquivalentOn
      chshLanguage
      chshPredictions
      classicalBounded
      violationPermitting)
chshViolationRefutesCandidateEquivalence =
  Physical.includedDiscriminatorRefutesEquivalence
    tt
    chshViolationDiscriminatesCandidateClasses

------------------------------------------------------------------------
-- Runtime receipt boundary.
--
-- The Python side must still establish that its measured/statistical CHSH
-- record belongs to the discrete `violatesClassicalBound` outcome under a
-- predeclared criterion.  This module starts *after* that classification.
------------------------------------------------------------------------

record CHSHRuntimeClassificationReceipt : Set₁ where
  constructor chshRuntimeClassificationReceipt
  field
    measurementProduced : Set
    classicalBoundCriterionDeclaredBeforeMeasurement : Set
    varianceCriterionSatisfied : Set
    observedOutcome : CHSHOutcome

open CHSHRuntimeClassificationReceipt public

record QuantumCHSHBoundary : Set where
  constructor quantumCHSHBoundary
  field
    runtimeAcceptedMeansEstablishedQuantumGravity : Bool
    runtimeAcceptedMeansEstablishedQuantumGravityIsFalse :
      runtimeAcceptedMeansEstablishedQuantumGravity ≡ false

    classifiedViolationSplitsCandidateClasses : Bool
    classifiedViolationSplitsCandidateClassesIsTrue :
      classifiedViolationSplitsCandidateClasses ≡ true

    chshCalibrationDischargesPhysicalPromotionGate : Bool
    chshCalibrationDischargesPhysicalPromotionGateIsFalse :
      chshCalibrationDischargesPhysicalPromotionGate ≡ false

canonicalQuantumCHSHBoundary : QuantumCHSHBoundary
canonicalQuantumCHSHBoundary =
  quantumCHSHBoundary
    false refl
    true refl
    false refl
