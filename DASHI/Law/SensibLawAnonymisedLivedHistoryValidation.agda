module DASHI.Law.SensibLawAnonymisedLivedHistoryValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Admissible
import DASHI.Law.SensibLawAnonymisedLivedHistoryHyperformalIntakeExact as Intake

------------------------------------------------------------------------
-- Narrow regression/validation surface for the anonymised lived-history lane.
------------------------------------------------------------------------

boundedProfessionalProjectionFactors :
  INF.FactorsThrough Intake.smallCaseProjection Intake.currentProfessionalConsumer
boundedProfessionalProjectionFactors =
  Intake.smallCaseFactorsForCurrentProfessionalQuestion

boundedProfessionalProjectionCannotReplaceWholeStory :
  INF.FactorsThrough Intake.smallCaseProjection Intake.storyContinuityConsumer → ⊥
boundedProfessionalProjectionCannotReplaceWholeStory =
  Intake.smallCaseCannotReplaceWholeStory

caseViewReopenable :
  Intake.sourceReopenable Intake.legalIntakeProjectionBoundary ≡ true
caseViewReopenable = refl

caseViewDoesNotDeleteOmittedHistory :
  Intake.omittedFromProjectionMeansDeleted Intake.legalIntakeProjectionBoundary ≡ false
caseViewDoesNotDeleteOmittedHistory = refl

recordingRibbonFlowDoesNotCreateTruth :
  Intake.createsTruth Intake.anonymisedRecordingFlow ≡ false
recordingRibbonFlowDoesNotCreateTruth = refl

recordingRibbonFlowDoesNotCreateAuthority :
  Intake.createsAuthority Intake.anonymisedRecordingFlow ≡ false
recordingRibbonFlowDoesNotCreateAuthority = refl

anonymisedFixtureContainsNoIdentifiers :
  Intake.containsRealWorldIdentifiers Intake.canonicalAnonymisedIntakeFixture ≡ false
anonymisedFixtureContainsNoIdentifiers = refl

anonymisedFixtureContainsNoDiagnosis :
  Intake.containsClinicalDiagnosis Intake.canonicalAnonymisedIntakeFixture ≡ false
anonymisedFixtureContainsNoDiagnosis = refl

anonymisedFixtureContainsNoAdjudicatedFinding :
  Intake.containsAdjudicatedFinding Intake.canonicalAnonymisedIntakeFixture ≡ false
anonymisedFixtureContainsNoAdjudicatedFinding = refl

captureReturnsToAnchoredThread :
  Admissible.step
    Intake.livedHistoryCaptureTransitionSystem
    Intake.returnToPriorThread
    Intake.currentSession
    Intake.sideThreadStored
  ≡ Intake.mainThreadAnchored
captureReturnsToAnchoredThread = refl
