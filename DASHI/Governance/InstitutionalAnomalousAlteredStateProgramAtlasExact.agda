module DASHI.Governance.InstitutionalAnomalousAlteredStateProgramAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.MenWhoStareAtGoatsEvidenceLayerExact as Goats
import DASHI.Governance.DrugGovernanceMultiAxisRepairPlannerExact as RepairPlanner

data ProgrammeFamily : Set where
  bluebirdArtichokeFamily mkultraMksearchFamily stargateGrillFlameFamily
  edgewoodHallucinogenFamily civilianPsychedelicResearchFamily : ProgrammeFamily

data PhenomenonFamily : Set where
  hypnosisSuggestion drugAlteredState isolationDeprivation remoteViewingPsi
  psychokineticExtraordinaryInfluence psychedelicTherapeuticEffect : PhenomenonFamily

data InstitutionalObjective : Set where
  interrogationControlObjective defensiveCountermeasureObjective
  intelligenceCollectionObjective militaryDisruptionObjective
  biomedicalTherapeuticObjective exploratoryMechanismObjective : InstitutionalObjective

data SubjectRelation : Set where
  volunteerParticipantRelation volunteerWithLimitedDisclosureRelation
  unwittingSubjectRelation patientParticipantRelation humanCognitiveParticipantRelation : SubjectRelation

data EfficacyStanding : Set where
  programmeExistenceOnly phenomenonReported mixedOrUnresolvedEfficacy
  operationalUtilityNotEstablished therapeuticEvidenceDeveloping : EfficacyStanding

record ProgrammeAtlasEntry : Set where
  constructor programmeAtlasEntry
  field
    programme : ProgrammeFamily
    phenomenon : PhenomenonFamily
    objective : InstitutionalObjective
    subjectRelation : SubjectRelation
    standing : EfficacyStanding
    sourceReference : String
    scopeReference : String
open ProgrammeAtlasEntry public

artichokeEntry : ProgrammeAtlasEntry
artichokeEntry = programmeAtlasEntry bluebirdArtichokeFamily hypnosisSuggestion
  interrogationControlObjective volunteerWithLimitedDisclosureRelation programmeExistenceOnly
  "CIA Project ARTICHOKE / BLUEBIRD records"
  "records drugs, hypnosis and isolation/interrogation research; does not establish efficacy of every proposed technique"

mkultraEntry : ProgrammeAtlasEntry
mkultraEntry = programmeAtlasEntry mkultraMksearchFamily drugAlteredState
  interrogationControlObjective unwittingSubjectRelation programmeExistenceOnly
  "1977 DCI testimony and CIA MKULTRA/MKSEARCH records"
  "some activities involved drugs/hypnosis and unwitting subjects; umbrella also included unrelated activities"

stargateEntry : ProgrammeAtlasEntry
stargateEntry = programmeAtlasEntry stargateGrillFlameFamily remoteViewingPsi
  intelligenceCollectionObjective humanCognitiveParticipantRelation operationalUtilityNotEstablished
  "CIA remote-viewing/STARGATE historical collection"
  "programme and human remote-viewing sessions documented; operational intelligence utility remains a separate consumer"

edgewoodEntry : ProgrammeAtlasEntry
edgewoodEntry = programmeAtlasEntry edgewoodHallucinogenFamily drugAlteredState
  militaryDisruptionObjective volunteerParticipantRelation mixedOrUnresolvedEfficacy
  "DoD/Health.mil Edgewood Arsenal hallucinogenic-agent studies"
  "service-member volunteer studies included psychochemicals and LSD field testing; volunteer status does not by itself settle adequacy of disclosure or modern consent standards"

psychedelicResearchEntry : ProgrammeAtlasEntry
psychedelicResearchEntry = programmeAtlasEntry civilianPsychedelicResearchFamily psychedelicTherapeuticEffect
  biomedicalTherapeuticObjective patientParticipantRelation therapeuticEvidenceDeveloping
  "peer-reviewed historical/clinical psychedelic research literature"
  "therapeutic research is not evidence for interrogation, remote viewing or extraordinary-influence claims"

data PublicOdditySurface : Set where sameInstitutionalOdditySurface : PublicOdditySurface

data AtlasWorld : Set where artichokeWorld stargateWorld psychedelicWorld : AtlasWorld

publicOddity : AtlasWorld → PublicOdditySurface
publicOddity _ = sameInstitutionalOdditySurface

worldObjective : AtlasWorld → InstitutionalObjective
worldObjective artichokeWorld = interrogationControlObjective
worldObjective stargateWorld = intelligenceCollectionObjective
worldObjective psychedelicWorld = biomedicalTherapeuticObjective

worldStanding : AtlasWorld → EfficacyStanding
worldStanding artichokeWorld = programmeExistenceOnly
worldStanding stargateWorld = operationalUtilityNotEstablished
worldStanding psychedelicWorld = therapeuticEvidenceDeveloping

objectiveDiffers : worldObjective artichokeWorld ≡ worldObjective stargateWorld → ⊥
objectiveDiffers ()

standingDiffers : worldStanding stargateWorld ≡ worldStanding psychedelicWorld → ⊥
standingDiffers ()

oddityCannotRecoverObjective : INF.FactorsThrough publicOddity worldObjective → ⊥
oddityCannotRecoverObjective = INF.witnessRulesOutEveryFlatFactorisation
  (INF.nonFactorabilityWitness artichokeWorld stargateWorld refl objectiveDiffers)

data AtlasConsumer : Set where
  programmeHistoryConsumer efficacyConsumer subjectEthicsConsumer therapeuticConsumer
  operationalUtilityConsumer institutionalRepairConsumer : AtlasConsumer

data AtlasDemand : AtlasConsumer → Set where
  programmeHistoryNeedsInstitutionalRecord : AtlasDemand programmeHistoryConsumer
  efficacyNeedsControlledEvidence : AtlasDemand efficacyConsumer
  subjectEthicsNeedsConsentAndExposureRecord : AtlasDemand subjectEthicsConsumer
  therapeuticUseNeedsClinicalEvidence : AtlasDemand therapeuticConsumer
  operationalUtilityNeedsOperationalEvaluation : AtlasDemand operationalUtilityConsumer
  repairNeedsIndependentHarmAndMandateReceipts : AtlasDemand institutionalRepairConsumer

stargateUtilityDemand : AtlasDemand operationalUtilityConsumer
stargateUtilityDemand = operationalUtilityNeedsOperationalEvaluation
mkultraEthicsDemand : AtlasDemand subjectEthicsConsumer
mkultraEthicsDemand = subjectEthicsNeedsConsentAndExposureRecord
psychedelicTherapeuticDemand : AtlasDemand therapeuticConsumer
psychedelicTherapeuticDemand = therapeuticUseNeedsClinicalEvidence

goatsBoundary : Goats.MenWhoStareAtGoatsEvidenceBoundary
goatsBoundary = Goats.canonicalMenWhoStareAtGoatsEvidenceBoundary
repairPlannerBoundary : RepairPlanner.MultiAxisRepairPlannerBoundary
repairPlannerBoundary = RepairPlanner.canonicalMultiAxisRepairPlannerBoundary

data WeirdnessPromotesProgrammeIdentity : Set where

data ProgrammeExistencePromotesEfficacy : Set where

data MilitaryResearchPromotesTherapeuticValidity : Set where

data TherapeuticEvidencePromotesPsiEfficacy : Set where

data InstitutionalInterestPromotesTruth : Set where

data EfficacyFailureErasesInstitutionalHistory : Set where

weirdnessDoesNotPromoteProgrammeIdentity : WeirdnessPromotesProgrammeIdentity → ⊥
weirdnessDoesNotPromoteProgrammeIdentity ()
programmeExistenceDoesNotPromoteEfficacy : ProgrammeExistencePromotesEfficacy → ⊥
programmeExistenceDoesNotPromoteEfficacy ()
militaryResearchDoesNotPromoteTherapeuticValidity : MilitaryResearchPromotesTherapeuticValidity → ⊥
militaryResearchDoesNotPromoteTherapeuticValidity ()
therapeuticEvidenceDoesNotPromotePsiEfficacy : TherapeuticEvidencePromotesPsiEfficacy → ⊥
therapeuticEvidenceDoesNotPromotePsiEfficacy ()
institutionalInterestDoesNotPromoteTruth : InstitutionalInterestPromotesTruth → ⊥
institutionalInterestDoesNotPromoteTruth ()
efficacyFailureDoesNotEraseInstitutionalHistory : EfficacyFailureErasesInstitutionalHistory → ⊥
efficacyFailureDoesNotEraseInstitutionalHistory ()

record InstitutionalAnomalousAlteredStateAtlasBoundary : Set where
  constructor institutionalAnomalousAlteredStateAtlasBoundary
  field
    programmePurposeAndPhenomenonAreSeparate : Bool
    programmePurposeAndPhenomenonAreSeparateIsTrue : programmePurposeAndPhenomenonAreSeparate ≡ true
    programmeExistenceProvesEfficacy : Bool
    programmeExistenceProvesEfficacyIsFalse : programmeExistenceProvesEfficacy ≡ false
    psychedelicEvidenceTransfersToPsi : Bool
    psychedelicEvidenceTransfersToPsiIsFalse : psychedelicEvidenceTransfersToPsi ≡ false
    failedPhenomenonMakesProgrammeHistoricallyUnreal : Bool
    failedPhenomenonMakesProgrammeHistoricallyUnrealIsFalse : failedPhenomenonMakesProgrammeHistoricallyUnreal ≡ false

canonicalInstitutionalAnomalousAlteredStateAtlasBoundary : InstitutionalAnomalousAlteredStateAtlasBoundary
canonicalInstitutionalAnomalousAlteredStateAtlasBoundary =
  institutionalAnomalousAlteredStateAtlasBoundary true refl false refl false refl false refl
