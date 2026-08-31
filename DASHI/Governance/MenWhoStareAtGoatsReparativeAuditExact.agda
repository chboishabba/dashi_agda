module DASHI.Governance.MenWhoStareAtGoatsReparativeAuditExact where

open import DASHI.Core.Prelude

import DASHI.Governance.MenWhoStareAtGoatsEvidenceLayerExact as Goats
import DASHI.Governance.DrugGovernanceMultiAxisReparativeFibreExact as Fibre
import DASHI.Governance.DrugGovernanceMultiAxisRepairPlannerExact as Planner

------------------------------------------------------------------------
-- MEN WHO STARE AT GOATS / MULTI-AXIS REPARATIVE AUDIT
--
-- This is a theorem-shape cross-pollination, not a claim that every programme
-- described by Ronson incurred every repair obligation.  Source verification,
-- causal/harm findings, repair need and authority to repair remain distinct.
------------------------------------------------------------------------

data InstitutionalHistoryResidual : Set where
  programmeHistoryResidual
  participantTreatmentResidual
  oversightResidual
  decisionRightsResidual
  nonRepetitionResidual
  extraordinaryClaimValidationResidual
  : InstitutionalHistoryResidual

residualProbe : InstitutionalHistoryResidual → Planner.RepairConsumer
residualProbe programmeHistoryResidual = Planner.truthHistoryConsumer
residualProbe participantTreatmentResidual = Planner.institutionalReformConsumer
residualProbe oversightResidual = Planner.institutionalReformConsumer
residualProbe decisionRightsResidual = Planner.decisionRightsConsumer
residualProbe nonRepetitionResidual = Planner.nonRepetitionConsumer
residualProbe extraordinaryClaimValidationResidual = Planner.truthHistoryConsumer

------------------------------------------------------------------------
-- BIDI: a documented institutional programme can justify a historical-audit
-- demand, but it does not manufacture a finding on every repair axis.
------------------------------------------------------------------------

programmeExistenceSupportsHistoryDemand :
  Goats.EvidenceDemand Goats.programmeExistedClaim
programmeExistenceSupportsHistoryDemand =
  Goats.programmeExistenceNeedsInstitutionalRecord

goatMechanismStillNeedsIndependentEvidence :
  Goats.EvidenceDemand Goats.goatKillingByStaringClaim
goatMechanismStillNeedsIndependentEvidence =
  Goats.goatKillingNeedsIndependentExperimentalEvidence

historyResidualSelectsTruthProbe :
  residualProbe programmeHistoryResidual ≡ Planner.truthHistoryConsumer
historyResidualSelectsTruthProbe = refl

nonRepetitionResidualSelectsNonRepetitionProbe :
  residualProbe nonRepetitionResidual ≡ Planner.nonRepetitionConsumer
nonRepetitionResidualSelectsNonRepetitionProbe = refl

------------------------------------------------------------------------
-- Non-promotions.
------------------------------------------------------------------------

data ProgrammeExistencePromotesRepairLiability : Set where

data ExtraordinaryClaimFailurePromotesParticipantHarm : Set where

data HistoricalTruthPromotesCompensation : Set where

data HistoricalTruthPromotesNonRepetitionClosure : Set where

data SatiricalRepresentationPromotesInstitutionalFact : Set where

data RepairAuditPromotesParanormalVerdict : Set where

programmeExistenceDoesNotPromoteRepairLiability :
  ProgrammeExistencePromotesRepairLiability → ⊥
programmeExistenceDoesNotPromoteRepairLiability ()

extraordinaryClaimFailureDoesNotPromoteParticipantHarm :
  ExtraordinaryClaimFailurePromotesParticipantHarm → ⊥
extraordinaryClaimFailureDoesNotPromoteParticipantHarm ()

historicalTruthDoesNotPromoteCompensation :
  HistoricalTruthPromotesCompensation → ⊥
historicalTruthDoesNotPromoteCompensation ()

historicalTruthDoesNotPromoteNonRepetitionClosure :
  HistoricalTruthPromotesNonRepetitionClosure → ⊥
historicalTruthDoesNotPromoteNonRepetitionClosure ()

satireDoesNotPromoteInstitutionalFact :
  SatiricalRepresentationPromotesInstitutionalFact → ⊥
satireDoesNotPromoteInstitutionalFact ()

repairAuditDoesNotPromoteParanormalVerdict :
  RepairAuditPromotesParanormalVerdict → ⊥
repairAuditDoesNotPromoteParanormalVerdict ()

------------------------------------------------------------------------
-- Reuse the actual multi-axis repair boundaries rather than defining a second
-- institutional-ethics ontology.
------------------------------------------------------------------------

repairBoundary : Fibre.DrugGovernanceMultiAxisReparativeBoundary
repairBoundary = Fibre.canonicalDrugGovernanceMultiAxisReparativeBoundary

plannerBoundary : Planner.MultiAxisRepairPlannerBoundary
plannerBoundary = Planner.canonicalMultiAxisRepairPlannerBoundary

goatsBoundary : Goats.MenWhoStareAtGoatsEvidenceBoundary
goatsBoundary = Goats.canonicalMenWhoStareAtGoatsEvidenceBoundary

record MenWhoStareAtGoatsReparativeAuditBoundary : Set where
  constructor menWhoStareAtGoatsReparativeAuditBoundary
  field
    institutionalHistoryCanTriggerRepairQuestions : Bool
    institutionalHistoryCanTriggerRepairQuestionsIsTrue :
      institutionalHistoryCanTriggerRepairQuestions ≡ true
    programmeExistenceAutomaticallyEstablishesRepairLiability : Bool
    programmeExistenceAutomaticallyEstablishesRepairLiabilityIsFalse :
      programmeExistenceAutomaticallyEstablishesRepairLiability ≡ false
    truthHistoryClosureAutomaticallyClosesOtherRepairAxes : Bool
    truthHistoryClosureAutomaticallyClosesOtherRepairAxesIsFalse :
      truthHistoryClosureAutomaticallyClosesOtherRepairAxes ≡ false
    repairAuditDeterminesParanormalEfficacy : Bool
    repairAuditDeterminesParanormalEfficacyIsFalse :
      repairAuditDeterminesParanormalEfficacy ≡ false

canonicalMenWhoStareAtGoatsReparativeAuditBoundary :
  MenWhoStareAtGoatsReparativeAuditBoundary
canonicalMenWhoStareAtGoatsReparativeAuditBoundary =
  menWhoStareAtGoatsReparativeAuditBoundary
    true refl false refl false refl false refl
