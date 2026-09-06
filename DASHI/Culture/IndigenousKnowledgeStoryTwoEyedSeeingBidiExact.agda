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
-- This is a source-bounded DASHI formal extension.  It does NOT define a
-- universal Indigenous epistemology.  Its finite witnesses preserve exactly
-- the distinctions that are otherwise easy to erase when a situated knowledge
-- practice is projected to a detached proposition or scientific result.
--
-- SOURCE CALIBRATION
--
-- Bartlett, Marshall & Marshall (2012), "Two-Eyed Seeing and other lessons
-- learned within a co-learning journey of bringing together indigenous and
-- mainstream knowledges and ways of knowing", Journal of Environmental
-- Studies and Sciences 2:331-340, DOI 10.1007/s13412-012-0086-8.
-- Bounded use: coordinated use of strengths from distinct knowledge systems
-- does not require epistemic fusion.
--
-- Kimmerer, Braiding Sweetgrass (2013), and Yunkaporta, Sand Talk (2019), are
-- inherited through existing DASHI source-bound owners.  No source is credited
-- with the finite factorisation theorems below.
--
-- National Film and Sound Archive of Australia, 2026 Creator Capsule,
-- "Outback Boys": Ramingining/Arnhem Land hunting, bushcraft and life on
-- Country through unscripted adventures, with Djambarrpuyngu spoken throughout;
-- the NFSA describes the channel as an immersive portrait of Yolngu knowledge
-- and identity.
-- https://www.nfsa.gov.au/stories/deep-dives/youtube-creator-capsule-outback-boys
--
-- ABC News (2017), "Black As returns to Ramingining for second season after
-- 'incredible demand'": bounded specimen for unscripted everyday ingenuity,
-- bush life and humour around the same Ramingining group.  Entertainment footage
-- is not treated as an exhaustive representation of Yolngu knowledge.
--
-- Montinari, Minelli & De Caterina (2019), "The first 3500 years of aspirin
-- history from its roots - A concise summary", Vascular Pharmacology 113:1-8,
-- DOI 10.1016/j.vph.2018.10.008.  Aspirin is used only as a calibration showing
-- long traditional plant-use -> chemistry -> manufactured-drug history; it is
-- NOT represented as a clean single-Indigenous-community discovery lineage.
--
-- Convention on Biological Diversity, Nagoya Protocol, especially Articles 5
-- and 12.  Bounded use: access/consent/community protocol/benefit-sharing remain
-- distinct from the downstream scientific result itself.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Knowledge carrier != extracted proposition.
------------------------------------------------------------------------

data KnowledgeContent : Set where
  medicinalPlantHelps : KnowledgeContent
  seasonalIndicator : KnowledgeContent
  repairWillHold : KnowledgeContent

data PlaceContext : Set where
  countryPlace : PlaceContext
  laboratoryPlace : PlaceContext

data PeopleRelation : Set where
  custodialRelation : PeopleRelation
  investigatorRelation : PeopleRelation

data PracticeContext : Set where
  livedPractice : PracticeContext
  controlledExperiment : PracticeContext

data TimeContext : Set where
  seasonalTime : TimeContext
  assayTime : TimeContext

data AuthorityStatus : Set where
  custodialAuthority : AuthorityStatus
  researchAuthority : AuthorityStatus

data PermissionStatus : Set where
  restrictedPermission : PermissionStatus
  openResearchPermission : PermissionStatus

data ObligationStatus : Set where
  reciprocalCare : ObligationStatus
  replicationReporting : ObligationStatus

data TransmissionMode : Set where
  story : TransmissionMode
  song : TransmissionMode
  demonstration : TransmissionMode
  directInstruction : TransmissionMode
  paper : TransmissionMode

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
    medicinalPlantHelps countryPlace custodialRelation livedPractice seasonalTime
    TwoEyed.indigenousHistory custodialAuthority restrictedPermission
    reciprocalCare story

scientificMedicinalPaperCarrier : KnowledgeCarrier
scientificMedicinalPaperCarrier =
  knowledgeCarrier
    medicinalPlantHelps laboratoryPlace investigatorRelation controlledExperiment
    assayTime TwoEyed.scientificHistory researchAuthority openResearchPermission
    replicationReporting paper

extractedProposition : KnowledgeCarrier -> KnowledgeContent
extractedProposition = content

carrierProvenance : KnowledgeCarrier -> TwoEyed.Provenance
carrierProvenance carrier = TwoEyed.provenance (knowledgeHistory carrier)

sameMedicinalPropositionAcrossHistories :
  extractedProposition indigenousMedicinalStoryCarrier
  ≡ extractedProposition scientificMedicinalPaperCarrier
sameMedicinalPropositionAcrossHistories = refl

propositionCannotRecoverProvenance :
  NonFactor.FactorsThrough extractedProposition carrierProvenance -> ⊥
propositionCannotRecoverProvenance =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      indigenousMedicinalStoryCarrier scientificMedicinalPaperCarrier refl (λ ()))

propositionCannotRecoverAuthority :
  NonFactor.FactorsThrough extractedProposition authority -> ⊥
propositionCannotRecoverAuthority =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      indigenousMedicinalStoryCarrier scientificMedicinalPaperCarrier refl (λ ()))

propositionCannotRecoverPermission :
  NonFactor.FactorsThrough extractedProposition permission -> ⊥
propositionCannotRecoverPermission =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      indigenousMedicinalStoryCarrier scientificMedicinalPaperCarrier refl (λ ()))

propositionCannotRecoverObligation :
  NonFactor.FactorsThrough extractedProposition obligation -> ⊥
propositionCannotRecoverObligation =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      indigenousMedicinalStoryCarrier scientificMedicinalPaperCarrier refl (λ ()))

------------------------------------------------------------------------
-- 2. Story surface != complete interpretation/authority.
------------------------------------------------------------------------

data StorySurface : Set where
  samePublicStory : StorySurface

data InterpretationLayer : Set where
  publicInterpretation : InterpretationLayer
  restrictedInterpretation : InterpretationLayer

data ListenerStanding : Set where
  publicListener : ListenerStanding
  authorisedCustodian : ListenerStanding

heardStory : ListenerStanding -> StorySurface
heardStory _ = samePublicStory

permittedInterpretation : ListenerStanding -> InterpretationLayer
permittedInterpretation publicListener = publicInterpretation
permittedInterpretation authorisedCustodian = restrictedInterpretation

hearingStoryCannotRecoverPermittedInterpretation :
  NonFactor.FactorsThrough heardStory permittedInterpretation -> ⊥
hearingStoryCannotRecoverPermittedInterpretation =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      publicListener authorisedCustodian refl (λ ()))

data NarrativeRole : Set where
  memoryCarrier : NarrativeRole
  transmissionCarrier : NarrativeRole
  interpretationCarrier : NarrativeRole
  governanceCarrier : NarrativeRole


narrativeCalibrationReuse : String
narrativeCalibrationReuse = Narrative.narrativeCalibrationReading

------------------------------------------------------------------------
-- 3. Two-Eyed Seeing coordination without fusion.
------------------------------------------------------------------------

record TwoEyedCoordination : Set where
  constructor twoEyedCoordination
  field
    indigenousCarrier : KnowledgeCarrier
    scientificCarrier : KnowledgeCarrier
    samePracticalContent :
      extractedProposition indigenousCarrier ≡ extractedProposition scientificCarrier
    indigenousHistoryExact :
      knowledgeHistory indigenousCarrier ≡ TwoEyed.indigenousHistory
    scientificHistoryExact :
      knowledgeHistory scientificCarrier ≡ TwoEyed.scientificHistory
    coordinatedUse : TwoEyed.CoordinatedUse

open TwoEyedCoordination public

canonicalTwoEyedMedicinalCoordination : TwoEyedCoordination
canonicalTwoEyedMedicinalCoordination =
  twoEyedCoordination
    indigenousMedicinalStoryCarrier scientificMedicinalPaperCarrier
    refl refl refl TwoEyed.useDistinctKnowledgesTogether

coordinatedConvergenceDoesNotFuseProvenance :
  TwoEyed.provenance TwoEyed.indigenousHistory
  ≡ TwoEyed.provenance TwoEyed.scientificHistory -> ⊥
coordinatedConvergenceDoesNotFuseProvenance = TwoEyed.provenanceDiffersAcrossHistories

sharedObservationStillCannotRecoverProvenance :
  NonFactor.FactorsThrough TwoEyed.observeKnowledgeHistory TwoEyed.provenance -> ⊥
sharedObservationStillCannotRecoverProvenance =
  TwoEyed.sharedObservationDoesNotRecoverProvenance

------------------------------------------------------------------------
-- 4. Translation can preserve, add, erase or leave coordinates unresolved.
------------------------------------------------------------------------

data TranslationStage : Set where
  situatedKnowledgeStage : TranslationStage
  extractedClaimStage : TranslationStage
  assayStage : TranslationStage
  mechanismStage : TranslationStage
  clinicalEvidenceStage : TranslationStage
  manufacturedMedicineStage : TranslationStage

data TranslationEffect : Set where
  preservesCoordinate : TranslationEffect
  addsCoordinate : TranslationEffect
  erasesCoordinate : TranslationEffect
  unresolvedCoordinate : TranslationEffect


data KnowledgeCoordinate : Set where
  contentCoordinate : KnowledgeCoordinate
  placeCoordinate : KnowledgeCoordinate
  relationCoordinate : KnowledgeCoordinate
  provenanceCoordinate : KnowledgeCoordinate
  authorityCoordinate : KnowledgeCoordinate
  permissionCoordinate : KnowledgeCoordinate
  obligationCoordinate : KnowledgeCoordinate
  mechanismCoordinate : KnowledgeCoordinate
  doseCoordinate : KnowledgeCoordinate
  toxicityCoordinate : KnowledgeCoordinate

selectedTranslationEffect : TranslationStage -> KnowledgeCoordinate -> TranslationEffect
selectedTranslationEffect situatedKnowledgeStage contentCoordinate = preservesCoordinate
selectedTranslationEffect situatedKnowledgeStage placeCoordinate = preservesCoordinate
selectedTranslationEffect situatedKnowledgeStage relationCoordinate = preservesCoordinate
selectedTranslationEffect situatedKnowledgeStage provenanceCoordinate = preservesCoordinate
selectedTranslationEffect situatedKnowledgeStage authorityCoordinate = preservesCoordinate
selectedTranslationEffect situatedKnowledgeStage permissionCoordinate = preservesCoordinate
selectedTranslationEffect situatedKnowledgeStage obligationCoordinate = preservesCoordinate
selectedTranslationEffect situatedKnowledgeStage mechanismCoordinate = unresolvedCoordinate
selectedTranslationEffect situatedKnowledgeStage doseCoordinate = unresolvedCoordinate
selectedTranslationEffect situatedKnowledgeStage toxicityCoordinate = unresolvedCoordinate
selectedTranslationEffect extractedClaimStage contentCoordinate = preservesCoordinate
selectedTranslationEffect extractedClaimStage placeCoordinate = erasesCoordinate
selectedTranslationEffect extractedClaimStage relationCoordinate = erasesCoordinate
selectedTranslationEffect extractedClaimStage provenanceCoordinate = erasesCoordinate
selectedTranslationEffect extractedClaimStage authorityCoordinate = erasesCoordinate
selectedTranslationEffect extractedClaimStage permissionCoordinate = erasesCoordinate
selectedTranslationEffect extractedClaimStage obligationCoordinate = erasesCoordinate
selectedTranslationEffect extractedClaimStage mechanismCoordinate = unresolvedCoordinate
selectedTranslationEffect extractedClaimStage doseCoordinate = unresolvedCoordinate
selectedTranslationEffect extractedClaimStage toxicityCoordinate = unresolvedCoordinate
selectedTranslationEffect assayStage contentCoordinate = preservesCoordinate
selectedTranslationEffect assayStage placeCoordinate = erasesCoordinate
selectedTranslationEffect assayStage relationCoordinate = erasesCoordinate
selectedTranslationEffect assayStage provenanceCoordinate = erasesCoordinate
selectedTranslationEffect assayStage authorityCoordinate = erasesCoordinate
selectedTranslationEffect assayStage permissionCoordinate = erasesCoordinate
selectedTranslationEffect assayStage obligationCoordinate = erasesCoordinate
selectedTranslationEffect assayStage mechanismCoordinate = addsCoordinate
selectedTranslationEffect assayStage doseCoordinate = addsCoordinate
selectedTranslationEffect assayStage toxicityCoordinate = unresolvedCoordinate
selectedTranslationEffect mechanismStage contentCoordinate = preservesCoordinate
selectedTranslationEffect mechanismStage placeCoordinate = erasesCoordinate
selectedTranslationEffect mechanismStage relationCoordinate = erasesCoordinate
selectedTranslationEffect mechanismStage provenanceCoordinate = erasesCoordinate
selectedTranslationEffect mechanismStage authorityCoordinate = erasesCoordinate
selectedTranslationEffect mechanismStage permissionCoordinate = erasesCoordinate
selectedTranslationEffect mechanismStage obligationCoordinate = erasesCoordinate
selectedTranslationEffect mechanismStage mechanismCoordinate = addsCoordinate
selectedTranslationEffect mechanismStage doseCoordinate = addsCoordinate
selectedTranslationEffect mechanismStage toxicityCoordinate = addsCoordinate
selectedTranslationEffect clinicalEvidenceStage contentCoordinate = preservesCoordinate
selectedTranslationEffect clinicalEvidenceStage placeCoordinate = erasesCoordinate
selectedTranslationEffect clinicalEvidenceStage relationCoordinate = erasesCoordinate
selectedTranslationEffect clinicalEvidenceStage provenanceCoordinate = erasesCoordinate
selectedTranslationEffect clinicalEvidenceStage authorityCoordinate = erasesCoordinate
selectedTranslationEffect clinicalEvidenceStage permissionCoordinate = erasesCoordinate
selectedTranslationEffect clinicalEvidenceStage obligationCoordinate = erasesCoordinate
selectedTranslationEffect clinicalEvidenceStage mechanismCoordinate = preservesCoordinate
selectedTranslationEffect clinicalEvidenceStage doseCoordinate = addsCoordinate
selectedTranslationEffect clinicalEvidenceStage toxicityCoordinate = addsCoordinate
selectedTranslationEffect manufacturedMedicineStage contentCoordinate = preservesCoordinate
selectedTranslationEffect manufacturedMedicineStage placeCoordinate = erasesCoordinate
selectedTranslationEffect manufacturedMedicineStage relationCoordinate = erasesCoordinate
selectedTranslationEffect manufacturedMedicineStage provenanceCoordinate = erasesCoordinate
selectedTranslationEffect manufacturedMedicineStage authorityCoordinate = erasesCoordinate
selectedTranslationEffect manufacturedMedicineStage permissionCoordinate = erasesCoordinate
selectedTranslationEffect manufacturedMedicineStage obligationCoordinate = erasesCoordinate
selectedTranslationEffect manufacturedMedicineStage mechanismCoordinate = preservesCoordinate
selectedTranslationEffect manufacturedMedicineStage doseCoordinate = preservesCoordinate
selectedTranslationEffect manufacturedMedicineStage toxicityCoordinate = preservesCoordinate

extractionErasesPlace :
  selectedTranslationEffect extractedClaimStage placeCoordinate ≡ erasesCoordinate
extractionErasesPlace = refl

assayCanAddMechanismInformation :
  selectedTranslationEffect assayStage mechanismCoordinate ≡ addsCoordinate
assayCanAddMechanismInformation = refl

manufacturedDrugDoesNotByItselfRestoreProvenance :
  selectedTranslationEffect manufacturedMedicineStage provenanceCoordinate
  ≡ erasesCoordinate
manufacturedDrugDoesNotByItselfRestoreProvenance = refl

------------------------------------------------------------------------
-- 5. Scientific result != consent != benefit sharing.
------------------------------------------------------------------------

data MedicinalTranslation : Set where
  situatedUseToCandidate : MedicinalTranslation
  candidateToAssay : MedicinalTranslation
  assayToMechanism : MedicinalTranslation
  mechanismToClinical : MedicinalTranslation
  clinicalToManufactured : MedicinalTranslation

data AccessStatus : Set where
  noAccessReceipt : AccessStatus
  priorInformedConsentReceipt : AccessStatus

data BenefitSharingStatus : Set where
  noBenefitSharingReceipt : BenefitSharingStatus
  mutuallyAgreedBenefitSharingReceipt : BenefitSharingStatus

data ScientificResultStatus : Set where
  candidateOnly : ScientificResultStatus
  activeCompoundFound : ScientificResultStatus
  mechanismCharacterised : ScientificResultStatus
  clinicalSupport : ScientificResultStatus


record MedicinalKnowledgeTranslationReceipt : Set where
  constructor medicinalKnowledgeTranslationReceipt
  field
    sourceCarrier : KnowledgeCarrier
    translation : MedicinalTranslation
    scientificResult : ScientificResultStatus
    accessStatus : AccessStatus
    benefitSharingStatus : BenefitSharingStatus

open MedicinalKnowledgeTranslationReceipt public

sameResultNoConsent : MedicinalKnowledgeTranslationReceipt
sameResultNoConsent =
  medicinalKnowledgeTranslationReceipt
    indigenousMedicinalStoryCarrier candidateToAssay activeCompoundFound
    noAccessReceipt noBenefitSharingReceipt

sameResultWithConsentAndBenefitSharing : MedicinalKnowledgeTranslationReceipt
sameResultWithConsentAndBenefitSharing =
  medicinalKnowledgeTranslationReceipt
    indigenousMedicinalStoryCarrier candidateToAssay activeCompoundFound
    priorInformedConsentReceipt mutuallyAgreedBenefitSharingReceipt

scientificResultCannotRecoverConsent :
  NonFactor.FactorsThrough scientificResult accessStatus -> ⊥
scientificResultCannotRecoverConsent =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      sameResultNoConsent sameResultWithConsentAndBenefitSharing refl (λ ()))

scientificResultCannotRecoverBenefitSharing :
  NonFactor.FactorsThrough scientificResult benefitSharingStatus -> ⊥
scientificResultCannotRecoverBenefitSharing =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      sameResultNoConsent sameResultWithConsentAndBenefitSharing refl (λ ()))

record NagoyaStylePromotionGate
    (receipt : MedicinalKnowledgeTranslationReceipt) : Set where
  constructor nagoyaStylePromotionGate
  field
    consentPresent : accessStatus receipt ≡ priorInformedConsentReceipt
    benefitSharingPresent :
      benefitSharingStatus receipt ≡ mutuallyAgreedBenefitSharingReceipt

------------------------------------------------------------------------
-- 6. Aspirin calibration.
------------------------------------------------------------------------

data AspirinHistoryStage : Set where
  ancientWillowUse : AspirinHistoryStage
  salicinIsolation : AspirinHistoryStage
  salicylicAcidChemistry : AspirinHistoryStage
  acetylsalicylicAcidManufacture : AspirinHistoryStage
  mechanismElucidation : AspirinHistoryStage

data AspirinHistoricalReading : Set where
  longTraditionalPlantUseLineage : AspirinHistoricalReading
  singleIndigenousDiscoveryLineage : AspirinHistoricalReading


aspirinBoundedReading : AspirinHistoricalReading
aspirinBoundedReading = longTraditionalPlantUseLineage

singleIndigenousDiscoveryIsNotBoundedAspirinReading :
  aspirinBoundedReading ≡ singleIndigenousDiscoveryLineage -> ⊥
singleIndigenousDiscoveryIsNotBoundedAspirinReading ()

------------------------------------------------------------------------
-- 7. Outback Boys / Black As as a contemporary situated-problem-solving
--    specimen: modern technology can coexist with Country knowledge.
------------------------------------------------------------------------

data ProblemKnowledgeDimension : Set where
  knowledgeThat : ProblemKnowledgeDimension
  knowledgeHow : ProblemKnowledgeDimension
  knowledgeWhen : ProblemKnowledgeDimension
  knowledgeWhere : ProblemKnowledgeDimension

data ProblemResource : Set where
  countryKnowledge : ProblemResource
  modernTechnology : ProblemResource
  embodiedSkill : ProblemResource
  availableMaterial : ProblemResource
  socialCoordination : ProblemResource
  storyMemory : ProblemResource

data RepairContext : Set where
  remoteCountryRepair : RepairContext
  workshopRepair : RepairContext

data RepairOutcome : Set where
  workingRepair : RepairOutcome

data RepairMethodSignature : Set where
  situatedImprovisedMethod : RepairMethodSignature
  canonicalWorkshopMethod : RepairMethodSignature

repairOutcome : RepairContext -> RepairOutcome
repairOutcome _ = workingRepair

repairMethod : RepairContext -> RepairMethodSignature
repairMethod remoteCountryRepair = situatedImprovisedMethod
repairMethod workshopRepair = canonicalWorkshopMethod

workingOutcomeCannotRecoverMethod :
  NonFactor.FactorsThrough repairOutcome repairMethod -> ⊥
workingOutcomeCannotRecoverMethod =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      remoteCountryRepair workshopRepair refl (λ ()))

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
    remoteCountryRepair countryKnowledge modernTechnology embodiedSkill
    availableMaterial socialCoordination storyMemory

modernTechnologyCoexistsWithCountryKnowledge :
  technicalKnowledge outbackBoysSourceBoundedSpecimen ≡ modernTechnology
modernTechnologyCoexistsWithCountryKnowledge = refl

countryKnowledgeRemainsExplicit :
  placeKnowledge outbackBoysSourceBoundedSpecimen ≡ countryKnowledge
countryKnowledgeRemainsExplicit = refl

------------------------------------------------------------------------
-- 8. Reuse existing situated-observation / relational-process boundaries.
------------------------------------------------------------------------

anonymousReadingStillCannotRecoverProvenance :
  NonFactor.FactorsThrough
    Situated.anonymousReading
    (λ observation -> TwoEyed.provenance (Situated.knowledgeHistory observation)) ->
  ⊥
anonymousReadingStillCannotRecoverProvenance =
  Situated.anonymousReadingCannotRecoverProvenance

relationalProcessSourceBoundary : Relational.RelationalEpistemicProcessBoundary
relationalProcessSourceBoundary = Relational.canonicalRelationalEpistemicProcessBoundary

------------------------------------------------------------------------
-- 9. Capstone no-promotion boundary.
------------------------------------------------------------------------

record IndigenousKnowledgeStoryTwoEyedBoundary : Set where
  constructor indigenousKnowledgeStoryTwoEyedBoundary
  field
    indigenousKnowledgeIsUniversalSetOfDetachedPropositions : Bool
    indigenousKnowledgeIsUniversalSetOfDetachedPropositionsIsFalse :
      indigenousKnowledgeIsUniversalSetOfDetachedPropositions ≡ false
    samePropositionMeansSameProvenance : Bool
    samePropositionMeansSameProvenanceIsFalse : samePropositionMeansSameProvenance ≡ false
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
    false refl false refl false refl false refl false refl false refl false refl
    false refl false refl false refl false refl false refl false refl false refl

open IndigenousKnowledgeStoryTwoEyedBoundary public
