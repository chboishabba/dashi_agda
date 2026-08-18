module DASHI.Education.EarlyLearningEvidenceRevisionHorizonExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.ReopenableEvidenceFibre as Reopenable
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Core.ProvenanceBearingQuotient as Quotient
import DASHI.Education.SituatedRelationalLearningAffordanceExact as Affordance

------------------------------------------------------------------------
-- VERSIONED EVIDENCE / MEASUREMENT HORIZON
--
-- The Quebec evidence surface changed as cohorts aged and as later maternal /
-- fiscal outcomes became observable.  This module treats evidence vintage and
-- outcome axis as explicit coordinates.  Later evidence may revise weighting
-- or reopen a policy assessment without erasing a still-valid receipt on a
-- different axis.
------------------------------------------------------------------------

data EvidenceVintage : Set where
  contemporaneousVintage schoolAgeVintage longRunVintage updatedFiscalVintage : EvidenceVintage

data EvidenceAxis : Set where
  childWellbeingAxis maternalLabourAxis caregiverWellbeingAxis fiscalAxis : EvidenceAxis

data EvidenceSignal : Set where
  adverseEvidence unresolvedEvidence beneficialEvidence : EvidenceSignal

record VersionedEvidenceObservation : Set where
  constructor versionedEvidenceObservation
  field
    vintage : EvidenceVintage
    axis : EvidenceAxis
    signal : EvidenceSignal

open VersionedEvidenceObservation public

quebecContemporaneousChild : VersionedEvidenceObservation
quebecContemporaneousChild =
  versionedEvidenceObservation contemporaneousVintage childWellbeingAxis adverseEvidence

quebecLongRunChild : VersionedEvidenceObservation
quebecLongRunChild =
  versionedEvidenceObservation longRunVintage childWellbeingAxis adverseEvidence

quebecUpdatedFiscal : VersionedEvidenceObservation
quebecUpdatedFiscal =
  versionedEvidenceObservation updatedFiscalVintage fiscalAxis beneficialEvidence

quebecMaternalLabour : VersionedEvidenceObservation
quebecMaternalLabour =
  versionedEvidenceObservation updatedFiscalVintage maternalLabourAxis beneficialEvidence

------------------------------------------------------------------------
-- A vintage label cannot determine the evidence signal.  The structural
-- witness deliberately holds the vintage fixed while varying the outcome axis.
------------------------------------------------------------------------

data SameUpdatedVintageCase : Set where
  updatedChildCase updatedFiscalCase : SameUpdatedVintageCase

updatedVintageProjection : SameUpdatedVintageCase → EvidenceVintage
updatedVintageProjection updatedChildCase = updatedFiscalVintage
updatedVintageProjection updatedFiscalCase = updatedFiscalVintage

updatedSignalAt : SameUpdatedVintageCase → EvidenceSignal
updatedSignalAt updatedChildCase = adverseEvidence
updatedSignalAt updatedFiscalCase = beneficialEvidence

updatedSignalsDiffer :
  updatedSignalAt updatedChildCase ≡ updatedSignalAt updatedFiscalCase → ⊥
updatedSignalsDiffer ()

vintageAloneCannotDetermineEvidenceSignal :
  Intersection.FactorsThrough updatedVintageProjection updatedSignalAt → ⊥
vintageAloneCannotDetermineEvidenceSignal =
  Intersection.witnessRulesOutEveryFlatFactorisation
    (Intersection.nonFactorabilityWitness
      updatedChildCase updatedFiscalCase refl updatedSignalsDiffer)

------------------------------------------------------------------------
-- Likewise one measurement horizon cannot stand in for the entire trajectory.
-- This reuses the already-declared developmental horizon carrier rather than
-- introducing another temporal ontology.
------------------------------------------------------------------------

data HorizonMatchedCase : Set where
  immediateAdverse immediateBeneficial : HorizonMatchedCase

horizonProjection : HorizonMatchedCase → Affordance.DevelopmentalMeasurementHorizon
horizonProjection immediateAdverse = Affordance.immediateSnapshot
horizonProjection immediateBeneficial = Affordance.immediateSnapshot

horizonSignal : HorizonMatchedCase → EvidenceSignal
horizonSignal immediateAdverse = adverseEvidence
horizonSignal immediateBeneficial = beneficialEvidence

horizonSignalsDiffer :
  horizonSignal immediateAdverse ≡ horizonSignal immediateBeneficial → ⊥
horizonSignalsDiffer ()

measurementHorizonCannotDetermineOutcomeDirection :
  Intersection.FactorsThrough horizonProjection horizonSignal → ⊥
measurementHorizonCannotDetermineOutcomeDirection =
  Intersection.witnessRulesOutEveryFlatFactorisation
    (Intersection.nonFactorabilityWitness
      immediateAdverse immediateBeneficial refl horizonSignalsDiffer)

------------------------------------------------------------------------
-- PNF reopening discipline.
--
-- We reuse the repository's canonical boundary directly: reweighting is not
-- refutation; suppression is not refutation; projection residual is not
-- semantic erasure.  Thus a new fiscal receipt cannot, merely by being later,
-- refute a distinct child-wellbeing receipt.
------------------------------------------------------------------------

canonicalReopenableEvidenceBoundary : Reopenable.ReopenableEvidenceBoundary
canonicalReopenableEvidenceBoundary = Reopenable.canonicalReopenableEvidenceBoundary

reweightingStillCannotRefute :
  Reopenable.ReweightingRefutationPermission → ⊥
reweightingStillCannotRefute = Reopenable.reweightingAloneCannotRefute

projectionResidualStillCannotEraseEvidence :
  Quotient.ProjectionSemanticErasurePermission Quotient.projectionReceiptOnly → ⊥
projectionResidualStillCannotEraseEvidence =
  Reopenable.ReopenableEvidenceBoundary.projectionResidualIsNotErasure
    canonicalReopenableEvidenceBoundary

------------------------------------------------------------------------
-- No source-ordering constructor converts newer evidence into authority to
-- erase older evidence on another axis.
------------------------------------------------------------------------

data LaterEvidenceErasesEarlierAxisPermission : Set where

laterEvidenceCannotEraseEarlierAxis :
  LaterEvidenceErasesEarlierAxisPermission → ⊥
laterEvidenceCannotEraseEarlierAxis ()

record EvidenceRevisionHorizonBoundary : Set where
  constructor evidenceRevisionHorizonBoundary
  field
    laterEvidenceAutomaticallyErasesEarlierEvidence : Bool
    laterEvidenceAutomaticallyErasesEarlierEvidenceIsFalse :
      laterEvidenceAutomaticallyErasesEarlierEvidence ≡ false
    oneHorizonDeterminesWholeTrajectory : Bool
    oneHorizonDeterminesWholeTrajectoryIsFalse :
      oneHorizonDeterminesWholeTrajectory ≡ false
    evidenceAssessmentRemainsReopenable : Bool
    evidenceAssessmentRemainsReopenableIsTrue :
      evidenceAssessmentRemainsReopenable ≡ true
    evidenceAxisAndVintageRemainDistinct : Bool
    evidenceAxisAndVintageRemainDistinctIsTrue :
      evidenceAxisAndVintageRemainDistinct ≡ true

canonicalEvidenceRevisionHorizonBoundary : EvidenceRevisionHorizonBoundary
canonicalEvidenceRevisionHorizonBoundary =
  evidenceRevisionHorizonBoundary false refl false refl true refl true refl
