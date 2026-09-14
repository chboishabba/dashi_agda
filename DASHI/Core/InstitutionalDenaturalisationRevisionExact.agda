module DASHI.Core.InstitutionalDenaturalisationRevisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.InstitutionalNormProductionExact as Norm
import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision

------------------------------------------------------------------------
-- APPEND-ONLY DENATURALISATION / BASELINE REINTERPRETATION
--
-- Later evidence about production history may change the currently justified
-- interpretation of an institutional baseline while preserving the earlier
-- observation and its provenance.  Denaturalisation therefore need not rewrite
-- history.  Conversely, reinterpretation does not automatically invalidate
-- every prior institutional act or prove that the earlier baseline was morally
-- justified.
------------------------------------------------------------------------

parentNormProductionBoundary : Norm.InstitutionalNormProductionBoundary
parentNormProductionBoundary = Norm.canonicalInstitutionalNormProductionBoundary

parentAppendOnlyRevisionBoundary : Revision.AppendOnlyEvidenceRevisionBoundary
parentAppendOnlyRevisionBoundary = Revision.canonicalAppendOnlyEvidenceRevisionBoundary

data InstitutionalEvidence : Set where
  baselineObservation : InstitutionalEvidence
  productionHistoryEvidence : InstitutionalEvidence

data InstitutionalEvidenceHistory : Set where
  baselineOnlyHistory : InstitutionalEvidenceHistory
  baselinePlusProductionHistory : InstitutionalEvidenceHistory

data InstitutionalInterpretation : Set where
  baselineTreatedAsGiven : InstitutionalInterpretation
  baselineRecognisedAsHistoricallyProduced : InstitutionalInterpretation

data BaselineContains : InstitutionalEvidence → InstitutionalEvidenceHistory → Set where
  baselineInBaselineOnly : BaselineContains baselineObservation baselineOnlyHistory
  baselineInExtended : BaselineContains baselineObservation baselinePlusProductionHistory
  productionHistoryInExtended :
    BaselineContains productionHistoryEvidence baselinePlusProductionHistory

appendInstitutionalEvidence :
  InstitutionalEvidenceHistory → InstitutionalEvidence → InstitutionalEvidenceHistory
appendInstitutionalEvidence baselineOnlyHistory baselineObservation = baselineOnlyHistory
appendInstitutionalEvidence baselineOnlyHistory productionHistoryEvidence =
  baselinePlusProductionHistory
appendInstitutionalEvidence baselinePlusProductionHistory evidence =
  baselinePlusProductionHistory

institutionalEvidencePersists :
  (history : InstitutionalEvidenceHistory) →
  (old new : InstitutionalEvidence) →
  BaselineContains old history →
  BaselineContains old (appendInstitutionalEvidence history new)
institutionalEvidencePersists
  baselineOnlyHistory baselineObservation baselineObservation baselineInBaselineOnly =
    baselineInBaselineOnly
institutionalEvidencePersists
  baselineOnlyHistory baselineObservation productionHistoryEvidence baselineInBaselineOnly =
    baselineInExtended
institutionalEvidencePersists
  baselinePlusProductionHistory baselineObservation new baselineInExtended =
    baselineInExtended
institutionalEvidencePersists
  baselinePlusProductionHistory productionHistoryEvidence new productionHistoryInExtended =
    productionHistoryInExtended

institutionalInterpretationAt :
  InstitutionalEvidenceHistory → InstitutionalInterpretation
institutionalInterpretationAt baselineOnlyHistory = baselineTreatedAsGiven
institutionalInterpretationAt baselinePlusProductionHistory =
  baselineRecognisedAsHistoricallyProduced

institutionalEvidenceSystem : Revision.AppendOnlyEvidenceSystem
institutionalEvidenceSystem = Revision.appendOnlyEvidenceSystem
  InstitutionalEvidence
  InstitutionalEvidenceHistory
  InstitutionalInterpretation
  appendInstitutionalEvidence
  BaselineContains
  institutionalEvidencePersists
  institutionalInterpretationAt
  (λ { baselineObservation → "observed institutional baseline"
     ; productionHistoryEvidence → "later production-history evidence" })
  (λ { baselineTreatedAsGiven → "baseline treated as given for current consumer"
     ; baselineRecognisedAsHistoricallyProduced →
         "baseline recognised as historically produced for current consumer" })

baselineInterpretationsDiffer :
  baselineTreatedAsGiven ≡ baselineRecognisedAsHistoricallyProduced → ⊥
baselineInterpretationsDiffer ()

InstitutionalInterpretationRevision : Set₁
InstitutionalInterpretationRevision =
  Revision.ConclusionRevision institutionalEvidenceSystem

canonicalInstitutionalInterpretationRevision : InstitutionalInterpretationRevision
canonicalInstitutionalInterpretationRevision = Revision.conclusionRevision
  baselineOnlyHistory
  productionHistoryEvidence
  baselineObservation
  baselineInBaselineOnly
  baselineInExtended
  baselineTreatedAsGiven
  baselineRecognisedAsHistoricallyProduced
  refl
  refl
  baselineInterpretationsDiffer
  "Production-history evidence is appended without deleting the prior baseline observation; the current interpretation changes for the declared consumer."

record InstitutionalDenaturalisationBoundary : Set where
  constructor institutionalDenaturalisationBoundary
  field
    parentNormProductionReused : Bool
    appendOnlyRevisionParentReused : Bool
    productionHistoryEvidenceMayChangeCurrentInterpretation : Bool
    laterEvidenceAutomaticallyRewritesEarlierObservation : Bool
    denaturalisationAutomaticallyInvalidatesEveryPriorInstitutionalAction : Bool
    priorBaselineObservationAutomaticallyMoralJustification : Bool
    changedInterpretationAutomaticallyChangesHistoricalEvent : Bool
    retainedPriorEvidenceAutomaticallyBlocksRevision : Bool

open InstitutionalDenaturalisationBoundary public

canonicalInstitutionalDenaturalisationBoundary : InstitutionalDenaturalisationBoundary
canonicalInstitutionalDenaturalisationBoundary =
  institutionalDenaturalisationBoundary
    true
    true
    true
    false
    false
    false
    false
    false
