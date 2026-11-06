module DASHI.Biology.Physical.BiologicalEvidenceFeedbackFiniteExact where

------------------------------------------------------------------------
-- BIOLOGICAL MECHANISM / EVIDENCE / REVISION FEEDBACK
--
-- Selected finite synthetic witness only. A discriminating observation
-- constrains a model family. Evidence reanalysis can reopen hypotheses.
-- This connects source-compatible temporal evidence fibres with an actual
-- selected biological transition law; it is NOT GO-CAM/SBML ingestion or
-- an empirical claim about planarian tissue or gene regulation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Evidence

data CandidateMechanism : Set where
  retainedMemoryMatters : CandidateMechanism
  presentMorphologyOnly : CandidateMechanism

-- Two competing predictions in the SAME selected finite model.
-- The second intentionally ignores hidden history, and so fails at the
-- explicit witness under the same intervention.
predictSignal : CandidateMechanism → Bio.BiologicalState → Bool
predictSignal retainedMemoryMatters state =
  Bio.observe (Bio.step Bio.signal state)
predictSignal presentMorphologyOnly state = Bio.observe state

data EvidenceStage : Set where
  unconstrained : EvidenceStage
  syntheticDiscrimination : EvidenceStage
  evidenceWithdrawn : EvidenceStage

Compatible : EvidenceStage → CandidateMechanism → Set
Compatible unconstrained candidate = ⊤
Compatible syntheticDiscrimination retainedMemoryMatters = ⊤
Compatible syntheticDiscrimination presentMorphologyOnly = ⊥
Compatible evidenceWithdrawn candidate = ⊤

data Summary : Set where
  sameVisibleSummary : Summary

sourceDescription : EvidenceStage → String
sourceDescription unconstrained =
  "unconstrained synthetic candidate-model family"
sourceDescription syntheticDiscrimination =
  "selected fixture: intervention-sensitive future response"
sourceDescription evidenceWithdrawn =
  "synthetic evidence withdrawn; candidate reopened"

modelEvidence : Evidence.TemporalEvidenceSystem
modelEvidence = record
  { Time = EvidenceStage
  ; Interpretation = CandidateMechanism
  ; Compatible = Compatible
  ; Summary = Summary
  ; summarize = λ stage → sameVisibleSummary
  ; timeReference = sourceDescription
  }

initialDependentCandidate :
  Evidence.EvidenceFibre modelEvidence unconstrained
initialDependentCandidate =
  Evidence.liveInterpretationAt retainedMemoryMatters tt

initialBlindCandidate :
  Evidence.EvidenceFibre modelEvidence unconstrained
initialBlindCandidate =
  Evidence.liveInterpretationAt presentMorphologyOnly tt

observedDependentCandidate :
  Evidence.EvidenceFibre modelEvidence syntheticDiscrimination
observedDependentCandidate =
  Evidence.liveInterpretationAt retainedMemoryMatters tt

blindCandidateRejected :
  Compatible syntheticDiscrimination presentMorphologyOnly → ⊥
blindCandidateRejected ()

syntheticObservationRefinesModelFamily :
  Evidence.StrictFibreRefinement
    modelEvidence unconstrained syntheticDiscrimination
syntheticObservationRefinesModelFamily = record
  { refinement = record
      { retainedWasPreviouslyLive = λ candidate evidence → tt }
  ; removedInterpretation = presentMorphologyOnly
  ; removedWasLive = tt
  ; removedIsNoLongerLive = blindCandidateRejected
  }

withdrawalReopensModelCandidate :
  Evidence.FibreReopening
    modelEvidence syntheticDiscrimination evidenceWithdrawn
withdrawalReopensModelCandidate = record
  { reopenedInterpretation = presentMorphologyOnly
  ; reopenedNowLive = tt
  ; reopenedWasNotLive = blindCandidateRejected
  }

presentSummaryEqualAcrossRevisions :
  Evidence.summarize modelEvidence syntheticDiscrimination
  ≡ Evidence.summarize modelEvidence evidenceWithdrawn
presentSummaryEqualAcrossRevisions = refl

retainedMemoryPrediction :
  predictSignal retainedMemoryMatters Bio.withMemory ≡ true
retainedMemoryPrediction = refl

memoryBlindPrediction :
  predictSignal presentMorphologyOnly Bio.withMemory ≡ false
memoryBlindPrediction = refl

memoryBlindMisfitsSyntheticObservation :
  predictSignal presentMorphologyOnly Bio.withMemory ≡ true → ⊥
memoryBlindMisfitsSyntheticObservation ()

-- These types are the model-side join obligations for external GO-CAM,
-- SBML, SI-calibrated measurements, and PNF evidence.  They deliberately
-- do not create an instance without a real source, model, and measurement.
record BiologicalSourceModelLoop : Set₁ where
  field
    Source Activity Reaction Parameter Context History Time Observation : Set
    activityFromSource : Source → Activity → Set
    reactionRealisesActivity : Activity → Reaction → Set
    parametersAdmissible : Reaction → Parameter → Set
    unitsValid : Parameter → Set
    predicts :
      Reaction → Parameter → Context → History → Time → Observation
    observationFromSource :
      Source → Context → History → Time → Observation → Set

record SourceCalibratedMechanism
    (loop : BiologicalSourceModelLoop) : Set₁ where
  open BiologicalSourceModelLoop loop
  field
    source : Source
    activity : Activity
    reaction : Reaction
    parameters : Parameter
    context : Context
    history : History
    time : Time
    measuredValue : Observation

    provenance : activityFromSource source activity
    mechanismJoin : reactionRealisesActivity activity reaction
    admissibleParameters : parametersAdmissible reaction parameters
    SIReceipt : unitsValid parameters
    observationReceipt :
      observationFromSource source context history time measuredValue
    predictionMatchesMeasurement :
      predicts reaction parameters context history time ≡ measuredValue

-- An inhabited finite proof cannot construct the missing evidence receipt.
record EvidenceFeedbackBoundary : Set where
  constructor evidenceFeedbackBoundary
  field
    toyEvidenceIsLaboratoryMeasurement : Bool
    toyEvidenceIsLaboratoryMeasurementFalse :
      toyEvidenceIsLaboratoryMeasurement ≡ false
    sourceIdentifierImpliesMechanism : Bool
    sourceIdentifierImpliesMechanismFalse :
      sourceIdentifierImpliesMechanism ≡ false
    evidenceRevisionAlwaysShrinksModelFamily : Bool
    evidenceRevisionAlwaysShrinksModelFamilyFalse :
      evidenceRevisionAlwaysShrinksModelFamily ≡ false
    typedSBMLJoinSuppliesKineticCalibration : Bool
    typedSBMLJoinSuppliesKineticCalibrationFalse :
      typedSBMLJoinSuppliesKineticCalibration ≡ false

canonicalEvidenceFeedbackBoundary : EvidenceFeedbackBoundary
canonicalEvidenceFeedbackBoundary =
  evidenceFeedbackBoundary false refl false refl false refl false refl
