module DASHI.Governance.ComparativeCrisisClimateAtlas where

open import Agda.Primitive using (Setω)
open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.RevolutionaryPracticeBraid as Practice
import DASHI.Governance.RevolutionarySourceAtlas as Source
import DASHI.Governance.TraumaMemorySublationBoundary as Trauma
import DASHI.Governance.Sudan.RCEPPInstitutionalSurface as RCEPP

------------------------------------------------------------------------
-- Comparative crisis / liberation / climate atlas.
--
-- Sudan remains the established constitutional case study.  Israel/Palestine,
-- Iran/USA, post-9/11 United States, the war-on-drugs grammar, contemporary
-- Trumpist memory spectacle and climate/social-justice pressure enter as
-- candidate comparative patterns.  The atlas does not equate histories,
-- organisations, power positions or tactics.
------------------------------------------------------------------------

data ComparativeCrisisContext : Set where
  sudanRCEPPContext : ComparativeCrisisContext
  israelPalestineComparativeContext : ComparativeCrisisContext
  iranUnitedStatesComparativeContext : ComparativeCrisisContext
  unitedStatesPostNineElevenComparativeContext : ComparativeCrisisContext
  warOnDrugsComparativeContext : ComparativeCrisisContext
  trumpismMemorySpectacleComparativeContext : ComparativeCrisisContext
  namedComparativeCrisisContext : String → ComparativeCrisisContext

data PalestinianLiberationCurrent : Set where
  secularNationalCurrent : PalestinianLiberationCurrent
  marxistPFLPCurrent : PalestinianLiberationCurrent
  islamistCurrent : PalestinianLiberationCurrent
  tradeUnionStudentWomenCurrent : PalestinianLiberationCurrent
  popularCommitteeCurrent : PalestinianLiberationCurrent
  diplomaticStateBuildingCurrent : PalestinianLiberationCurrent
  culturalIntellectualCurrent : PalestinianLiberationCurrent
  diasporaCurrent : PalestinianLiberationCurrent
  namedPalestinianCurrent : String → PalestinianLiberationCurrent

canonicalPalestinianLiberationCurrents : List PalestinianLiberationCurrent
canonicalPalestinianLiberationCurrents =
  secularNationalCurrent
  ∷ marxistPFLPCurrent
  ∷ islamistCurrent
  ∷ tradeUnionStudentWomenCurrent
  ∷ popularCommitteeCurrent
  ∷ diplomaticStateBuildingCurrent
  ∷ culturalIntellectualCurrent
  ∷ diasporaCurrent
  ∷ []

record LiberationPracticeAssessment : Set where
  constructor liberationPracticeAssessment
  field
    practiceLabel : String
    declaredEnd : String
    socialBase : String
    organisationalForm : String
    meansSurface : String
    civilianHarmAccountabilityRequired : Bool
    internalAccountabilityRequired : Bool
    ecologicalProgrammeInspected : Bool
    pluralismToleranceInspected : Bool
    liberatoryObjectiveAutomaticallyLegitimatesEveryTactic : Bool
    tacticCondemnationErasesUnderlyingLiberationClaim : Bool
    organisationalLabelClosesHistoricalAnalysis : Bool
    formalAssessmentCreatesDesignationAuthority : Bool
    formalAssessmentCreatesPoliticalAuthority : Bool

open LiberationPracticeAssessment public

mkLiberationPracticeAssessment :
  String → String → String → String → String → LiberationPracticeAssessment
mkLiberationPracticeAssessment label end base form means =
  liberationPracticeAssessment
    label
    end
    base
    form
    means
    true
    true
    true
    true
    false
    false
    false
    false
    false

pflpPracticeAssessment : LiberationPracticeAssessment
pflpPracticeAssessment =
  mkLiberationPracticeAssessment
    "Popular Front for the Liberation of Palestine (PFLP)"
    "Palestinian national liberation within a Marxist anti-imperialist current"
    "Palestinian organisational, popular and diaspora constituencies; historically variable"
    "party/front organisation within a plural Palestinian liberation field"
    "armed, political, organisational and cultural means require tactic-specific historical and civilian-harm review"

palestinianPopularCommitteeAssessment : LiberationPracticeAssessment
palestinianPopularCommitteeAssessment =
  mkLiberationPracticeAssessment
    "Palestinian popular committee practice"
    "local self-organisation, resistance, service, participation and community capacity"
    "affected local communities"
    "committee / local coordination"
    "civil, organisational and locally variable resistance practices"

record ComparativeCasePattern : Set where
  constructor comparativeCasePattern
  field
    caseContext : ComparativeCrisisContext
    caseLabel : String
    historicalFrames : List Trauma.HistoricalOriginFrame
    sourceReferences : List Source.SourceReference
    traumaRecognitionRequired : Bool
    materialPowerAsymmetryVisible : Bool
    civilianProtectionRequired : Bool
    selectedOriginCompleteCause : Bool
    traumaParityImpliesPowerParity : Bool
    oneOrganisationRepresentsWholePeople : Bool
    organisationLabelDeterminesEveryTactic : Bool
    formalComparisonCreatesHistoricalEquivalence : Bool
    formalComparisonCreatesPoliticalAuthority : Bool

open ComparativeCasePattern public

mkComparativeCasePattern :
  ComparativeCrisisContext →
  String →
  List Trauma.HistoricalOriginFrame →
  List Source.SourceReference →
  ComparativeCasePattern
mkComparativeCasePattern context label frames sources =
  comparativeCasePattern
    context
    label
    frames
    sources
    true
    true
    true
    false
    false
    false
    false
    false
    false

sudanComparativePattern : ComparativeCasePattern
sudanComparativePattern =
  mkComparativeCasePattern
    sudanRCEPPContext
    "Sudan / RCEPP popular-power reconstruction"
    (Trauma.sudanAprilTwentyTwentyThreeFrame ∷ [])
    []

israelPalestineComparativePattern : ComparativeCasePattern
israelPalestineComparativePattern =
  mkComparativeCasePattern
    israelPalestineComparativeContext
    "Israel / Palestine plural trauma, dispossession, occupation, resistance and radical power asymmetry"
    (Trauma.israelPalestinePluralOriginFrame ∷ [])
    (Source.edwardSaidQuestionOfPalestine
      ∷ Source.rashidKhalidiHundredYearsWar
      ∷ Source.judithButlerFramesOfWar
      ∷ Source.frantzFanonWretchedEarth
      ∷ [])

iranUnitedStatesComparativePattern : ComparativeCasePattern
iranUnitedStatesComparativePattern =
  mkComparativeCasePattern
    iranUnitedStatesComparativeContext
    "Iran / United States recursive intervention, revolution, siege, retaliation and threat narration"
    (Trauma.iranNineteenFiftyThreeFrame
      ∷ Trauma.iranNineteenSeventyNineFrame
      ∷ [])
    (Source.ervandAbrahamianTheCoup ∷ [])

unitedStatesPostNineElevenComparativePattern : ComparativeCasePattern
unitedStatesPostNineElevenComparativePattern =
  mkComparativeCasePattern
    unitedStatesPostNineElevenComparativeContext
    "United States post-9/11 trauma and war-on-terror repetition"
    (Trauma.unitedStatesNineElevenFrame ∷ [])
    (Source.nineElevenCommissionReport
      ∷ Source.dominickLaCapraWritingHistoryWritingTrauma
      ∷ Source.judithButlerFramesOfWar
      ∷ [])

warOnDrugsComparativePattern : ComparativeCasePattern
warOnDrugsComparativePattern =
  mkComparativeCasePattern
    warOnDrugsComparativeContext
    "war-on-drugs enemy-carrier and punitive-state grammar"
    []
    (Source.kimberleCrenshawMappingMargins ∷ [])

trumpismMemorySpectacleComparativePattern : ComparativeCasePattern
trumpismMemorySpectacleComparativePattern =
  mkComparativeCasePattern
    trumpismMemorySpectacleComparativeContext
    "Trumpist traumatic-restoration and agonistic memory-spectacle candidate pattern"
    []
    (Source.toddGitlinTheSixties
      ∷ Source.judithButlerFramesOfWar
      ∷ [])

canonicalComparativeCasePatterns : List ComparativeCasePattern
canonicalComparativeCasePatterns =
  sudanComparativePattern
  ∷ israelPalestineComparativePattern
  ∷ iranUnitedStatesComparativePattern
  ∷ unitedStatesPostNineElevenComparativePattern
  ∷ warOnDrugsComparativePattern
  ∷ trumpismMemorySpectacleComparativePattern
  ∷ []

data ClimateJusticeAxis : Set where
  foodWaterSecurityAxis : ClimateJusticeAxis
  displacementAxis : ClimateJusticeAxis
  landAndLivelihoodAxis : ClimateJusticeAxis
  urbanPressureAxis : ClimateJusticeAxis
  energyGeopoliticsAxis : ClimateJusticeAxis
  borderMilitarisationAxis : ClimateJusticeAxis
  disasterOpportunismAxis : ClimateJusticeAxis
  unequalRecoveryCapacityAxis : ClimateJusticeAxis

canonicalClimateJusticeAxes : List ClimateJusticeAxis
canonicalClimateJusticeAxes =
  foodWaterSecurityAxis
  ∷ displacementAxis
  ∷ landAndLivelihoodAxis
  ∷ urbanPressureAxis
  ∷ energyGeopoliticsAxis
  ∷ borderMilitarisationAxis
  ∷ disasterOpportunismAxis
  ∷ unequalRecoveryCapacityAxis
  ∷ []

record ClimateConflictBoundary : Set where
  constructor climateConflictBoundary
  field
    axes : List ClimateJusticeAxis
    climatePressureMaterial : Bool
    unequalLandRelationsMaterial : Bool
    militarisationMaterial : Bool
    institutionalCapacityMaterial : Bool
    historicalDispossessionMaterial : Bool
    climatePressureAloneCausesWar : Bool
    climateExplanationErasesPoliticalResponsibility : Bool
    formalClimateModelCreatesCausalAuthority : Bool

open ClimateConflictBoundary public

canonicalClimateConflictBoundary : ClimateConflictBoundary
canonicalClimateConflictBoundary =
  climateConflictBoundary
    canonicalClimateJusticeAxes
    true
    true
    true
    true
    true
    false
    false
    false

record EcologicalPeaceRepairSurface : Set where
  constructor ecologicalPeaceRepairSurface
  field
    civilianSafetyRequired : Bool
    landRepairRequired : Bool
    voluntaryReturnRequired : Bool
    reciprocityRequired : Bool
    materialJusticeRequired : Bool
    ecologicalContinuanceRequired : Bool
    affectedCommunityParticipationRequired : Bool
    armedEliteAgreementAloneSufficient : Bool
    publicOwnershipAloneEqualsReciprocity : Bool
    formalSurfaceEstablishesPeace : Bool

open EcologicalPeaceRepairSurface public

canonicalEcologicalPeaceRepairSurface : EcologicalPeaceRepairSurface
canonicalEcologicalPeaceRepairSurface =
  ecologicalPeaceRepairSurface
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false

record GlobalAttentionResidual : Set where
  constructor globalAttentionResidual
  field
    sufferingScaleEqualsAttention : Bool
    geopoliticalCentralityShapesAttention : Bool
    mediaInfrastructureShapesAttention : Bool
    racialisedIdentificationShapesAttention : Bool
    spectacleCompatibilityShapesAttention : Bool
    ignoredCrisisMeansMinorCrisis : Bool
    formalAttentionModelMeasuresActualConcern : Bool

open GlobalAttentionResidual public

canonicalGlobalAttentionResidual : GlobalAttentionResidual
canonicalGlobalAttentionResidual =
  globalAttentionResidual
    false
    true
    true
    true
    true
    false
    false

record ComparativeCrisisClimateAtlasSurface : Setω where
  constructor comparativeCrisisClimateAtlasSurface
  field
    practiceBraid : Practice.RevolutionaryPracticeBraidSurface
    traumaBoundary : Trauma.TraumaMemoryCrossPollination
    rceppPeaceSurface : RCEPP.RCEPPPeaceReconstructionSurface
    palestinianCurrents : List PalestinianLiberationCurrent
    liberationAssessments : List LiberationPracticeAssessment
    cases : List ComparativeCasePattern
    climateBoundary : ClimateConflictBoundary
    ecologicalPeaceSurface : EcologicalPeaceRepairSurface
    attentionResidual : GlobalAttentionResidual
    sudanIsReducedToAnalogy : Bool
    casesAreHistoricallyEquivalent : Bool
    liberationGoalsAutomaticallyLegitimateTactics : Bool
    stateDesignationAutomaticallyClosesAnalysis : Bool
    climateJusticeIsOptionalAppendix : Bool
    formalAtlasCreatesPoliticalAuthority : Bool

open ComparativeCrisisClimateAtlasSurface public

canonicalComparativeCrisisClimateAtlasSurface :
  ComparativeCrisisClimateAtlasSurface
canonicalComparativeCrisisClimateAtlasSurface =
  comparativeCrisisClimateAtlasSurface
    Practice.canonicalRevolutionaryPracticeBraidSurface
    Trauma.canonicalTraumaMemoryCrossPollination
    RCEPP.canonicalRCEPPPeaceReconstructionSurface
    canonicalPalestinianLiberationCurrents
    (pflpPracticeAssessment ∷ palestinianPopularCommitteeAssessment ∷ [])
    canonicalComparativeCasePatterns
    canonicalClimateConflictBoundary
    canonicalEcologicalPeaceRepairSurface
    canonicalGlobalAttentionResidual
    false
    false
    false
    false
    false
    false

record ComparativeCrisisClimateAtlasBoundary : Set where
  constructor comparativeCrisisClimateAtlasBoundary
  field
    pflpGoalDoesNotLegitimateEveryTactic :
      liberatoryObjectiveAutomaticallyLegitimatesEveryTactic
        pflpPracticeAssessment
        ≡ false
    tacticCritiqueDoesNotEraseLiberationClaim :
      tacticCondemnationErasesUnderlyingLiberationClaim
        pflpPracticeAssessment
        ≡ false
    climateDoesNotActAsSoleCause :
      climatePressureAloneCausesWar canonicalClimateConflictBoundary
        ≡ false
    attentionDoesNotMeasureSuffering :
      sufferingScaleEqualsAttention canonicalGlobalAttentionResidual
        ≡ false
    casesDoNotCollapseToEquivalence :
      casesAreHistoricallyEquivalent canonicalComparativeCrisisClimateAtlasSurface
        ≡ false
    politicalAuthorityBlocked :
      formalAtlasCreatesPoliticalAuthority
        canonicalComparativeCrisisClimateAtlasSurface
        ≡ false

open ComparativeCrisisClimateAtlasBoundary public

canonicalComparativeCrisisClimateAtlasBoundary :
  ComparativeCrisisClimateAtlasBoundary
canonicalComparativeCrisisClimateAtlasBoundary =
  comparativeCrisisClimateAtlasBoundary refl refl refl refl refl refl

canonicalComparativeCrisisClimateAtlasReceipt :
  GenericReceipt.GenericReceipt
canonicalComparativeCrisisClimateAtlasReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "comparative crisis liberation and climate atlas"
    "DASHI.Governance.ComparativeCrisisClimateAtlas"
    "canonicalComparativeCrisisClimateAtlasSurface"
    "keeps Sudan/RCEPP as the situated constitutional case while adding non-equating Israel/Palestine, Iran/USA, post-9/11, war-on-drugs, Trumpist memory-spectacle, Palestinian liberation-plurality, global-attention and climate-justice pattern lanes"
    "the atlas does not endorse organisations or tactics, create terrorism/designation authority, equate histories, infer motives, prove climate causation, establish peace or create political authority"
    "agda -i . DASHI/Governance/ComparativeCrisisClimateAtlas.agda"
