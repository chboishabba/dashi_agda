module DASHI.Core.ExternalisationMatchedControlScoringExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TechnicalExternalisationDepthBidiExact as X
import DASHI.Core.ReferencePopulationRosterEnrichmentExact as R

------------------------------------------------------------------------
-- MATCHED-CONTROL SCORING FOR TECHNICAL EXTERNALISATION DEPTH
--
-- Missing evidence is not absence. A control is scored with the same stage
-- rubric as a roster work, and the deep-externalisation predicate only closes
-- from positive stage receipts for model + method + validation.
------------------------------------------------------------------------

data StageEvidenceState : Set where
  stagePresent
  stageAbsent
  stageNotInspected
  stageConflict
  : StageEvidenceState

record StageEvidenceReceipt : Set where
  constructor stage-evidence-receipt
  field
    stage : X.ExternalisationStage
    state : StageEvidenceState
    sourceReference : String
    boundedReading : String

open StageEvidenceReceipt public

record MatchedExternalisationSubject : Set where
  constructor matched-externalisation-subject
  field
    subjectName : String
    stratum : String
    matchingReference : String
    stageReceipts : List StageEvidenceReceipt

open MatchedExternalisationSubject public

record PositiveStage
    (subject : MatchedExternalisationSubject)
    (target : X.ExternalisationStage) : Set where
  constructor positive-stage
  field
    receipt : StageEvidenceReceipt
    receiptInSubject : StageEvidenceReceipt ∈ stageReceipts subject
    correctStage : stage receipt ≡ target
    present : state receipt ≡ stagePresent

open PositiveStage public

record DeepExternalisationScore
    (subject : MatchedExternalisationSubject) : Set where
  constructor deep-externalisation-score
  field
    modelPositive : PositiveStage subject X.physicalOrTechnicalModel
    methodPositive : PositiveStage subject X.algorithmOrDesignMethod
    validationPositive : PositiveStage subject X.benchmarkOrValidation
    scoringReference : String

open DeepExternalisationScore public

------------------------------------------------------------------------
-- A complete score is stronger than a deep-positive witness. It requires every
-- stage to have been inspected rather than silently treating unknowns as false.
------------------------------------------------------------------------

record StageInspectionComplete (receipt : StageEvidenceReceipt) : Set where
  constructor stage-inspection-complete
  field
    inspected :
      (state receipt ≡ stagePresent) ⊎
      (state receipt ≡ stageAbsent) ⊎
      (state receipt ≡ stageConflict)

open StageInspectionComplete public

record SubjectScoringComplete (subject : MatchedExternalisationSubject) : Set where
  constructor subject-scoring-complete
  field
    eachReceiptInspected :
      (receipt : StageEvidenceReceipt) →
      receipt ∈ stageReceipts subject →
      StageInspectionComplete receipt
    completenessReference : String

open SubjectScoringComplete public

record ExternalisationControlCohort : Set where
  constructor externalisation-control-cohort
  field
    design : R.MatchedReferenceDesign
    rosterSubjects : List MatchedExternalisationSubject
    controlSubjects : List MatchedExternalisationSubject
    cohortReference : String

open ExternalisationControlCohort public

record ExternalisationControlBoundary : Set where
  constructor externalisation-control-boundary
  field
    notInspectedCountsAsAbsent : Bool
    notInspectedCountsAsAbsentIsFalse : notInspectedCountsAsAbsent ≡ false
    profilePageAloneCompletesPublicationDepthScore : Bool
    profilePageAloneCompletesPublicationDepthScoreIsFalse :
      profilePageAloneCompletesPublicationDepthScore ≡ false
    controlMayBeDroppedBecauseItExternalisesMore : Bool
    controlMayBeDroppedBecauseItExternalisesMoreIsFalse :
      controlMayBeDroppedBecauseItExternalisesMore ≡ false
    sameRubricRequiredForRosterAndControls : Bool
    sameRubricRequiredForRosterAndControlsIsTrue :
      sameRubricRequiredForRosterAndControls ≡ true
    enrichmentRequiresCompletedComparableScores : Bool
    enrichmentRequiresCompletedComparableScoresIsTrue :
      enrichmentRequiresCompletedComparableScores ≡ true

canonicalExternalisationControlBoundary : ExternalisationControlBoundary
canonicalExternalisationControlBoundary = externalisation-control-boundary
  false refl
  false refl
  false refl
  true refl
  true refl
