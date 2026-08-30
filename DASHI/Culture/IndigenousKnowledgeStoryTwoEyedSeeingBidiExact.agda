module DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.RelationalEpistemicProcessSourceBridgeExact as Relational
import DASHI.Culture.KimmererNarrativeMetaphorCalibrationExact as Narrative
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Environment.LESSituatedObservationInteractionExact as Situated

------------------------------------------------------------------------
-- INDIGENOUS KNOWLEDGE / STORY / TWO-EYED SEEING BIDI CAPSTONE
--
-- PURPOSE
--
-- This module formalises repository-native boundaries exposed by a discussion
-- about Indigenous knowledge, storytelling, Two-Eyed Seeing, medicinal
-- knowledge translation and contemporary Yolngu situated problem solving.
--
-- It does NOT define a universal Indigenous epistemology.  The finite carriers
-- below are deliberately synthetic theorem witnesses.  They preserve several
-- distinctions that are easy to erase when Indigenous knowledge is reduced to
-- an extracted proposition or a Western scientific validation surface.
--
-- SOURCE CALIBRATION
--
-- Cheryl Bartlett, Murdena Marshall, Albert Marshall (2012),
-- "Two-Eyed Seeing and other lessons learned within a co-learning journey of
-- bringing together indigenous and mainstream knowledges and ways of knowing",
-- Journal of Environmental Studies and Sciences 2:331-340,
-- DOI 10.1007/s13412-012-0086-8.
-- Bounded use: motivates coordinated use of strengths from distinct knowledge
-- systems without requiring epistemic fusion.
--
-- Robin Wall Kimmerer, Braiding Sweetgrass (2013).
-- Bounded use: inherited through the existing DASHI Kimmerer owners for
-- relational, narrative and provenance-sensitive interpretation.
--
-- Tyson Yunkaporta, Sand Talk (2019).
-- Bounded use: inherited through RelationalEpistemicProcessSourceBridgeExact;
-- no source vocabulary is identified with DASHI theorem constructors.
--
-- National Film and Sound Archive of Australia, 2026 Creator Capsule:
-- "Outback Boys".  The NFSA describes the Ramingining/Arnhem Land channel as
-- documenting hunting, bushcraft and life on Country through largely unscripted
-- adventures, with Djambarrpuyngu spoken throughout, and as an immersive
-- portrait of Yolngu knowledge and identity.
-- https://www.nfsa.gov.au/stories/deep-dives/youtube-creator-capsule-outback-boys
-- Bounded use: source specimen for contemporary situated problem solving,
-- storytelling and co-presence of Country knowledge with modern technology.
--
-- ABC News (2017), "Black As returns to Ramingining for second season after
-- 'incredible demand'".  Bounded use: source specimen for unscripted everyday
-- problem-solving, ingenuity, bush life and humour around the same Ramingining
-- group.  No claim is made that entertainment footage exhausts Yolngu knowledge.
--
-- Maria Rosa Montinari, Sergio Minelli, Raffaele De Caterina (2019),
-- "The first 3500 years of aspirin history from its roots - A concise summary",
-- Vascular Pharmacology 113:1-8, DOI 10.1016/j.vph.2018.10.008.
-- Bounded use: aspirin is retained only as a calibration example showing a
-- long traditional-use -> chemistry -> manufactured-drug history; it is NOT
-- represented as a clean single-Indigenous-community discovery lineage.
--
-- Convention on Biological Diversity, Nagoya Protocol, especially Articles 5
-- and 12.  Bounded use: motivates keeping access, prior informed consent,
-- community protocols and benefit-sharing distinct from mere scientific use of
-- traditional knowledge associated with genetic resources.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. A knowledge carrier is richer than an extracted proposition.
------------------------------------------------------------------------

data KnowledgeContent : Set where
  medicinalPlantHelps seasonalIndicator repairWillHold : KnowledgeContent

data PlaceContext : Set where
  countryPlace laboratoryPlace : PlaceContext

data PeopleRelation : Set where
  custodialRelation investigatorRelation : PeopleRelation

data PracticeContext : Set where
  livedPractice controlledExperiment : PracticeContext

data TimeContext : Set where
  seasonalTime assayTime : TimeContext

data AuthorityStatus : Set where
  custodialAuthority researchAuthority : AuthorityStatus

data PermissionStatus : Set where
  restrictedPermission openResearchPermission : PermissionStatus

data ObligationStatus : Set where
  reciprocalCare replicationReporting : ObligationStatus

data TransmissionMode : Set where
  story song demonstration directInstruction paper : TransmissionMode

record KnowledgeCarrier : Set where
  constructor knowledgeCarrier
  field
    content : KnowledgeContent
    place : PlaceContext
    peopleRelation : PeopleRelation
    practice : PracticeContext
    time : TimeContext
    knowledgeHistory : TwoEyed.KnowledgeHistory
    authority : AuthorityStatus
    permission : PermissionStatus
    obligation : ObligationStatus
    transmission : TransmissionMode

open KnowledgeCarrier public

indigenousMedicinalStoryCarrier : KnowledgeCarrier
indigenousMedicinalStoryCarrier =
  knowledgeCarrier
    medicinalPlantHelps
    countryPlace
    custodialRelation
    livedPractice
    seasonalTime
    TwoEyed.indigenousHistory
    custodialAuthority
    restrictedPermission
    reciprocalCare
    story

scientificMedicinalPaperCarrier : KnowledgeCarrier
scientificMedicinalPaperCarrier =
  knowledgeCarrier
    medicinalPlantHelps
    laboratoryPlace
    investigatorRelation
    controlledExperiment
    assayTime
    TwoEyed.scientificHistory
    researchAuthority
    openResearchPermission
    replicationReporting
    paper

extractedProposition : KnowledgeCarrier → KnowledgeContent
extractedProposition = content

carrierProvenance : KnowledgeCarrier → TwoEyed.Provenance
carrierProvenance carrier = TwoEyed.provenance (knowledgeHistory carrier)

sameMedicinalPropositionAcrossHistories :
  extractedProposition indigenousMedicinalStoryCarrier
  ≡ extractedProposition scientificMedicinalPaperCarrier
sameMedicinalPropositionAcrossHistories = refl

samePropositionDifferentProvenance :
  carrierProvenance indigenousMedicinalStoryCarrier
  ≡ carrierProvenance scientificMedicinalPaperCarrier → ⊥
samePropositionDifferentProvenance ()

propositionCannotRecoverProvenance :
  NonFactor.FactorsThrough extractedProposition carrierProvenance → ⊥
propositionCannotRecoverProvenance =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      indigenousMedicinalStoryCarrier
      scientificMedicinalPaperCarrier
      refl
      (λ ()))

propositionCannotRecoverAuthority :
  NonFactor.FactorsThrough extractedProposition authority → ⊥
propositionCannotRecoverAuthority =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      indigenousMedicinalStoryCarrier
      scientificMedicinalPaperCarrier
      refl
      (λ ()))

propositionCannotRecoverPermission :
  NonFactor.FactorsThrough extractedProposition permission → ⊥
propositionCannotRecoverPermission =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      indigenousMedicinalStoryCarrier
      scientificMedicinalPaperCarrier
      refl
      (λ ()))

propositionCannotRecoverObligation :
  NonFactor.FactorsThrough extractedProposition obligation → ⊥
propositionCannotRecoverObligation =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      indigenousMedicinalStoryCarrier
      scientificMedicinalPaperCarrier
      refl
      (λ ()))

------------------------------------------------------------------------
-- 2. Story is a knowledge expression, not proof that every listener possesses
--    every interpretation or permission carried by the source relation.
------------------------------------------------------------------------

data StorySurface : Set where
  samePublicStory : StorySurface

data InterpretationLayer : Set where
  publicInterpretation restrictedInterpretation : InterpretationLayer

data ListenerStanding : Set where
  publicListener authorisedCustodian : ListenerStanding

heardStory : ListenerStanding → StorySurface
heardStory _ = samePublicStory

permittedInterpretation : ListenerStanding → InterpretationLayer
permittedInterpretation publicListener = publicInterpretation
permittedInterpretation authorisedCustodian = restrictedInterpretation

sameStorySurfaceAcrossStandings :
  heardStory publicListener ≡ heardStory authorisedCustodian
sameStorySurfaceAcrossStandings = refl

hearingStoryCannotRecoverPermittedInterpretation :
  NonFactor.FactorsThrough heardStory permittedInterpretation → ⊥
hearingStoryCannotRecoverPermittedInterpretation =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      publicListener
      authorisedCustodian
      refl
      (λ ()))

data NarrativeRole : Set where
  memoryCarrier transmissionCarrier interpretationCarrier governanceCarrier
  : NarrativeRole

storyCanCarryMemory : NarrativeRole
storyCanCarryMemory = memoryCarrier

storyCanCarryTransmission : NarrativeRole
storyCanCarryTransmission = transmissionCarrier

storyCanCarryInterpretation : NarrativeRole
storyCanCarryInterpretation = interpretationCarrier

storyCanCarryGovernance : NarrativeRole
storyCanCarryGovernance = governanceCarrier

narrativeCalibrationReuse : String
narrativeCalibrationReuse = Narrative.narrativeCalibrationReading

------------------------------------------------------------------------
-- 3. Two-Eyed Seeing: coordinated use without identity or forced fusion.
------------------------------------------------------------------------

record TwoEyedCoordination : Set where
  constructor twoEyedCoordination
  field
    indigenousCarrier : KnowledgeCarrier
    scientificCarrier : KnowledgeCarrier
    samePracticalContent :
      extractedProposition indigenousCarrier
      ≡ extractedProposition scientificCarrier
    indigenousHistoryExact :
      knowledgeHistory indigenousCarrier ≡ TwoEyed.indigenousHistory
    scientificHistoryExact :
      knowledgeHistory scientificCarrier ≡ TwoEyed.scientificHistory
    coordinatedUse : TwoEyed.CoordinatedUse

open TwoEyedCoordination public

canonicalTwoEyedMedicinalCoordination : TwoEyedCoordination
canonicalTwoEyedMedicinalCoordination =
  twoEyedCoordination
    indigenousMedicinalStoryCarrier
    scientificMedicinalPaperCarrier
    refl
    refl
    refl
    TwoEyed.useDistinctKnowledgesTogether

coordinatedConvergenceDoesNotFuseProvenance :
  TwoEyed.provenance TwoEyed.indigenousHistory
  ≡ TwoEyed.provenance TwoEyed.scientificHistory → ⊥
coordinatedConvergenceDoesNotFuseProvenance =
  TwoEyed.provenanceDiffersAcrossHistories

sharedObservationStillCannotRecoverProvenance :
  NonFactor.FactorsThrough
    TwoEyed.observeKnowledgeHistory
    TwoEyed.provenance → ⊥
sharedObservationStillCannotRecoverProvenance =
  TwoEyed.sharedObservationDoesNotRecoverProvenance

------------------------------------------------------------------------
-- 4. Translation is partial and may add or erase coordinates.
------------------------------------------------------------------------

data TranslationStage : Set where
  situatedKnowledgeStage extractedClaimStage assayStage mechanismStage
  clinicalEvidenceStage manufacturedMedicineStage : TranslationStage

data TranslationEffect : Set where
  preservesCoordinate addsCoordinate erasesCoordinate unresolvedCoordinate
  : TranslationEffect

data KnowledgeCoordinate : Set where
  contentCoordinate placeCoordinate relationCoordinate practiceCoordinate
  provenanceCoordinate authorityCoordinate permissionCoordinate
  obligationCoordinate mechanismCoordinate doseCoordinate toxicityCoordinate
  : KnowledgeCoordinate

translationEffect : TranslationStage → KnowledgeCoordinate → TranslationEffect
translationEffect situatedKnowledgeStage contentCoordinate = preservesCoordinate
translationEffect situatedKnowledgeStage placeCoordinate = preservesCoordinate
translationEffect situatedKnowledgeStage relationCoordinate = preservesCoordinate
translationEffect situatedKnowledgeStage practiceCoordinate = preservesCoordinate
translationEffect situatedKnowledgeStage provenanceCoordinate = preservesCoordinate
translationEffect situatedKnowledgeStage authorityCoordinate = preservesCoordinate
translationEffect situatedKnowledgeStage permissionCoordinate = preservesCoordinate
translationEffect situatedKnowledgeStage obligationCoordinate = preservesCoordinate
translationEffect situatedKnowledgeStage mechanismCoordinate = unresolvedCoordinate
translationEffect situatedKnowledgeStage doseCoordinate = unresolvedCoordinate
translationEffect situatedKnowledgeStage toxicityCoordinate = unresolvedCoordinate
translationEffect extractedClaimStage contentCoordinate = preservesCoordinate
translationEffect extractedClaimStage placeCoordinate = erasesCoordinate
translationEffect extractedClaimStage relationCoordinate = erasesCoordinate
translationEffect extractedClaimStage practiceCoordinate = erasesCoordinate
translationEffect extractedClaimStage provenanceCoordinate = erasesCoordinate
translationEffect extractedClaimStage authorityCoordinate = erasesCoordinate
translationEffect extractedClaimStage permissionCoordinate = erasesCoordinate
translationEffect extractedClaimStage obligationCoordinate = erasesCoordinate
translationEffect extractedClaimStage mechanismCoordinate = unresolvedCoordinate
translationEffect extractedClaimStage doseCoordinate = unresolvedCoordinate
translationEffect extractedClaimStage toxicityCoordinate = unresolvedCoordinate
translationEffect assayStage contentCoordinate = preservesCoordinate
translationEffect assayStage placeCoordinate = erasesCoordinate
translationEffect assayStage relationCoordinate = erasesCoordinate
translationEffect assayStage practiceCoordinate = erasesCoordinate
translationEffect assayStage provenanceCoordinate = erasesCoordinate
translationEffect assayStage authorityCoordinate = erasesCoordinate
translationEffect assayStage permissionCoordinate = erasesCoordinate
translationEffect assayStage obligationCoordinate = erasesCoordinate
translationEffect assayStage mechanismCoordinate = addsCoordinate
translationEffect assayStage doseCoordinate = addsCoordinate
translationEffect assayStage toxicityCoordinate = unresolvedCoordinate
translationEffect mechanismStage contentCoordinate = preservesCoordinate
translationEffect mechanismStage placeCoordinate = erasesCoordinate
translationEffect mechanismStage relationCoordinate = erasesCoordinate
translationEffect mechanismStage practiceCoordinate = erasesCoordinate
translationEffect mechanismStage provenanceCoordinate = erasesCoordinate
translationEffect mechanismStage authorityCoordinate = erasesCoordinate
translationEffect mechanismStage permissionCoordinate = erasesCoordinate
translationEffect mechanismStage obligationCoordinate = erasesCoordinate
translationEffect mechanismStage mechanismCoordinate = addsCoordinate
translationEffect mechanismStage doseCoordinate = addsCoordinate
translationEffect mechanismStage toxicityCoordinate = addsCoordinate
translationEffect clinicalEvidenceStage contentCoordinate = preservesCoordinate
translationEffect clinicalEvidenceStage placeCoordinate = erasesCoordinate
translationEffect clinicalEvidenceStage relationCoordinate = erasesCoordinate
translationEffect clinicalEvidenceStage practiceCoordinate = erasesCoordinate
translationEffect clinicalEvidenceStage provenanceCoordinate = erasesCoordinate
translationEffect clinicalEvidenceStage authorityCoordinate = erasesCoordinate
translationEffect clinicalEvidenceStage permissionCoordinate = erasesCoordinate
translationEffect clinicalEvidenceStage obligationCoordinate = erasesCoordinate
translationEffect clinicalEvidenceStage mechanismCoordinate = preservesCoordinate
translationEffect clinicalEvidenceStage doseCoordinate = addsCoordinate
translationEffect clinicalEvidenceStage toxicityCoordinate = addsCoordinate
translationEffect manufacturedMedicineStage contentCoordinate = preservesCoordinate
translationEffect manufacturedMedicineStage placeCoordinate = erasesCoordinate
translationEffect manufacturedMedicineStage relationCoordinate = erasesCoordinate
translationEffect manufacturedMedicineStage practiceCoordinate = erasesCoordinate
translationEffect manufacturedMedicineStage provenanceCoordinate = erasesCoordinate
translationEffect manufacturedMedicineStage authorityCoordinate = erasesCoordinate
translationEffect manufacturedMedicineStage permissionCoordinate = erasesCoordinate
translationEffect manufacturedMedicineStage obligationCoordinate = erasesCoordinate
translationEffect manufacturedMedicineStage mechanismCoordinate = preservesCoordinate
translationEffect manufacturedMedicineStage doseCoordinate = preservesCoordinate
translationEffect manufacturedMedicineStage toxicityCoordinate = preservesCoordinate

extractionErasesPlace :
  translationEffect extractedClaimStage placeCoordinate ≡ erasesCoordinate
extractionErasesPlace = refl

assayCanAddMechanismInformation :
  translationEffect assayStage mechanismCoordinate ≡ addsCoordinate
assayCanAddMechanismInformation = refl

manufacturedDrugDoesNotByItselfRestoreProvenance :
  translationEffect manufacturedMedicineStage provenanceCoordinate
  ≡ erasesCoordinate
manufacturedDrugDoesNotByItselfRestoreProvenance = refl

------------------------------------------------------------------------
-- 5. Medicinal-knowledge translation and benefit-sharing are separate axes.
------------------------------------------------------------------------

data MedicinalTranslation : Set where
  situatedUseToCandidate candidateToAssay assayToMechanism mechanismToClinical
  clinicalToManufactured : MedicinalTranslation

data AccessStatus : Set where
  noAccessReceipt priorInformedConsentReceipt : AccessStatus

data BenefitSharingStatus : Set where
  noBenefitSharingReceipt mutuallyAgreedBenefitSharingReceipt
  : BenefitSharingStatus

data ScientificResultStatus : Set where
  candidateOnly activeCompoundFound mechanismCharacterised clinicalSupport
  : ScientificResultStatus

record MedicinalKnowledgeTranslationReceipt : Set where
  constructor medicinalKnowledgeTranslationReceipt
  field
    sourceCarrier : KnowledgeCarrier
    translation : MedicinalTranslation
    scientificResult : ScientificResultStatus
    accessStatus : AccessStatus
    benefitSharingStatus : BenefitSharingStatus

open MedicinalKnowledgeTranslationReceipt public

scientificResultDoesNotDetermineConsent :
  ScientificResultStatus → AccessStatus
scientificResultDoesNotDetermineConsent _ = noAccessReceipt

scientificResultDoesNotDetermineBenefitSharing :
  ScientificResultStatus → BenefitSharingStatus
scientificResultDoesNotDetermineBenefitSharing _ = noBenefitSharingReceipt

record NagoyaStylePromotionGate
    (receipt : MedicinalKnowledgeTranslationReceipt) : Set where
  constructor nagoyaStylePromotionGate
  field
    consentPresent : accessStatus receipt ≡ priorInformedConsentReceipt
    benefitSharingPresent :
      benefitSharingStatus receipt ≡ mutuallyAgreedBenefitSharingReceipt

------------------------------------------------------------------------
-- Aspirin calibration: traditional plant use can precede scientific chemistry,
-- while "aspirin came from Indigenous knowledge" is too coarse as a historical
-- identity claim for the well-known willow lineage.
------------------------------------------------------------------------

data AspirinHistoryStage : Set where
  ancientWillowUse salicinIsolation salicylicAcidChemistry
  acetylsalicylicAcidManufacture mechanismElucidation : AspirinHistoryStage

data AspirinHistoricalReading : Set where
  longTraditionalPlantUseLineage singleIndigenousDiscoveryLineage
  : AspirinHistoricalReading

aspirinBoundedReading : AspirinHistoricalReading
aspirinBoundedReading = longTraditionalPlantUseLineage

singleIndigenousDiscoveryIsNotBoundedAspirinReading :
  aspirinBoundedReading ≡ singleIndigenousDiscoveryLineage → ⊥
singleIndigenousDiscoveryIsNotBoundedAspirinReading ()

------------------------------------------------------------------------
-- 6. Contemporary situated problem solving: Outback Boys / Black As specimen.
------------------------------------------------------------------------

data ProblemKnowledgeDimension : Set where
  knowledgeThat knowledgeHow knowledgeWhen knowledgeWhere : ProblemKnowledgeDimension

data ProblemResource : Set where
  countryKnowledge modernTechnology embodiedSkill availableMaterial
  socialCoordination storyMemory : ProblemResource

data RepairContext : Set where
  remoteCountryRepair workshopRepair : RepairContext

data RepairOutcome : Set where
  workingRepair : RepairOutcome

data RepairMethodSignature : Set where
  situatedImprovisedMethod canonicalWorkshopMethod : RepairMethodSignature

repairOutcome : RepairContext → RepairOutcome
repairOutcome _ = workingRepair

repairMethod : RepairContext → RepairMethodSignature
repairMethod remoteCountryRepair = situatedImprovisedMethod
repairMethod workshopRepair = canonicalWorkshopMethod

sameWorkingOutcomeDifferentMethod :
  repairOutcome remoteCountryRepair ≡ repairOutcome workshopRepair
sameWorkingOutcomeDifferentMethod = refl

workingOutcomeCannotRecoverMethod :
  NonFactor.FactorsThrough repairOutcome repairMethod → ⊥
workingOutcomeCannotRecoverMethod =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      remoteCountryRepair
      workshopRepair
      refl
      (λ ()))

record SituatedProblemSolving : Set where
  constructor situatedProblemSolving
  field
    context : RepairContext
    placeKnowledge : ProblemResource
    technicalKnowledge : ProblemResource
    embodiedKnowledge : ProblemResource
    localMaterials : ProblemResource
    coordination : ProblemResource
    narrativeMemory : ProblemResource

open SituatedProblemSolving public

outbackBoysSourceBoundedSpecimen : SituatedProblemSolving
outbackBoysSourceBoundedSpecimen =
  situatedProblemSolving
    remoteCountryRepair
    countryKnowledge
    modernTechnology
    embodiedSkill
    availableMaterial
    socialCoordination
    storyMemory

modernTechnologyCoexistsWithCountryKnowledge :
  technicalKnowledge outbackBoysSourceBoundedSpecimen ≡ modernTechnology
modernTechnologyCoexistsWithCountryKnowledge = refl

countryKnowledgeRemainsExplicit :
  placeKnowledge outbackBoysSourceBoundedSpecimen ≡ countryKnowledge
countryKnowledgeRemainsExplicit = refl

storyMemoryRemainsExplicit :
  narrativeMemory outbackBoysSourceBoundedSpecimen ≡ storyMemory
storyMemoryRemainsExplicit = refl

------------------------------------------------------------------------
-- 7. Reuse the repo's existing situated-observation and relational-process
--    boundaries instead of replacing them.
------------------------------------------------------------------------

anonymousReadingStillCannotRecoverProvenance :
  NonFactor.FactorsThrough
    Situated.anonymousReading
    (λ observation → TwoEyed.provenance (Situated.knowledgeHistory observation)) →
  ⊥
anonymousReadingStillCannotRecoverProvenance =
  Situated.anonymousReadingCannotRecoverProvenance

relationalProcessSourceBoundary : Relational.RelationalEpistemicProcessBoundary
relationalProcessSourceBoundary = Relational.canonicalRelationalEpistemicProcessBoundary

------------------------------------------------------------------------
-- 8. Capstone no-promotion boundary.
------------------------------------------------------------------------

record IndigenousKnowledgeStoryTwoEyedBoundary : Set where
  constructor indigenousKnowledgeStoryTwoEyedBoundary
  field
    indigenousKnowledgeIsUniversalSetOfDetachedPropositions : Bool
    indigenousKnowledgeIsUniversalSetOfDetachedPropositionsIsFalse :
      indigenousKnowledgeIsUniversalSetOfDetachedPropositions ≡ false

    samePropositionMeansSameProvenance : Bool
    samePropositionMeansSameProvenanceIsFalse :
      samePropositionMeansSameProvenance ≡ false

    hearingStoryMeansPossessingEveryInterpretation : Bool
    hearingStoryMeansPossessingEveryInterpretationIsFalse :
      hearingStoryMeansPossessingEveryInterpretation ≡ false

    hearingStoryMeansPermissionToDiscloseOrUse : Bool
    hearingStoryMeansPermissionToDiscloseOrUseIsFalse :
      hearingStoryMeansPermissionToDiscloseOrUse ≡ false

    twoEyedSeeingRequiresEpistemicFusion : Bool
    twoEyedSeeingRequiresEpistemicFusionIsFalse :
      twoEyedSeeingRequiresEpistemicFusion ≡ false

    scientificValidationCreatesPriorKnowledgeFromNothing : Bool
    scientificValidationCreatesPriorKnowledgeFromNothingIsFalse :
      scientificValidationCreatesPriorKnowledgeFromNothing ≡ false

    activeCompoundIdentificationRecoversWholeSourceKnowledgeSystem : Bool
    activeCompoundIdentificationRecoversWholeSourceKnowledgeSystemIsFalse :
      activeCompoundIdentificationRecoversWholeSourceKnowledgeSystem ≡ false

    scientificResultAutomaticallyProvesConsent : Bool
    scientificResultAutomaticallyProvesConsentIsFalse :
      scientificResultAutomaticallyProvesConsent ≡ false

    scientificResultAutomaticallyProvesBenefitSharing : Bool
    scientificResultAutomaticallyProvesBenefitSharingIsFalse :
      scientificResultAutomaticallyProvesBenefitSharing ≡ false

    aspirinIsCleanSingleIndigenousDiscoveryExample : Bool
    aspirinIsCleanSingleIndigenousDiscoveryExampleIsFalse :
      aspirinIsCleanSingleIndigenousDiscoveryExample ≡ false

    usingModernTechnologyReplacesIndigenousKnowledge : Bool
    usingModernTechnologyReplacesIndigenousKnowledgeIsFalse :
      usingModernTechnologyReplacesIndigenousKnowledge ≡ false

    entertainmentFootageExhaustsYolnguKnowledge : Bool
    entertainmentFootageExhaustsYolnguKnowledgeIsFalse :
      entertainmentFootageExhaustsYolnguKnowledge ≡ false

    sameSuccessfulRepairMeansSameMethodOrContext : Bool
    sameSuccessfulRepairMeansSameMethodOrContextIsFalse :
      sameSuccessfulRepairMeansSameMethodOrContext ≡ false

    dashiFiniteCarrierIsUniversalIndigenousEpistemology : Bool
    dashiFiniteCarrierIsUniversalIndigenousEpistemologyIsFalse :
      dashiFiniteCarrierIsUniversalIndigenousEpistemology ≡ false

canonicalIndigenousKnowledgeStoryTwoEyedBoundary :
  IndigenousKnowledgeStoryTwoEyedBoundary
canonicalIndigenousKnowledgeStoryTwoEyedBoundary =
  indigenousKnowledgeStoryTwoEyedBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
