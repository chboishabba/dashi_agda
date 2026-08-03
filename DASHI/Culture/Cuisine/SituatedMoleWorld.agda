module DASHI.Culture.Cuisine.SituatedMoleWorld where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.HyperfabricIntersectionalBodyMemoryBridge as Hyper
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Culture.KnotWeaveTopologyCultureBridge as Knot
import DASHI.Culture.Cuisine.MoleProcessArchitecture as Process
import DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas as Sources
import DASHI.Interop.SweetgrassCarrierSpine as Sweetgrass

------------------------------------------------------------------------
-- Mole as a situated social, ecological, historical and political world.
--
-- The edible dish is a projection of this world, not its complete inverse.
-- Structural comparison with braid, weave, PatternMind or hyperfabric remains
-- bounded and does not identify distinct Indigenous peoples or ontologies.
------------------------------------------------------------------------

data FoodSystemStage : Set where
  agriculturalReproductionStage : FoodSystemStage
  harvestSelectionStage : FoodSystemStage
  postharvestProcessingStage : FoodSystemStage
  kitchenPreparationStage : FoodSystemStage
  collectiveCookingStage : FoodSystemStage
  commensalEatingStage : FoodSystemStage
  ritualMemoryStage : FoodSystemStage

canonicalFoodSystemStages : List FoodSystemStage
canonicalFoodSystemStages =
  agriculturalReproductionStage
  ∷ harvestSelectionStage
  ∷ postharvestProcessingStage
  ∷ kitchenPreparationStage
  ∷ collectiveCookingStage
  ∷ commensalEatingStage
  ∷ ritualMemoryStage
  ∷ []

record TraditionalFoodSystem : Set where
  constructor traditionalFoodSystem
  field
    systemLabel : String
    territory : String
    community : String
    stages : List FoodSystemStage
    cultivatedKinds : List String
    associatedKinds : List String
    seedLineages : List String
    seasonalCalendar : String
    waterRelations : String
    soilPractices : String
    ritualRelations : String
    exchangeRelations : String
    systemReading : String

open TraditionalFoodSystem public

canonicalMilpaFoodSystem : TraditionalFoodSystem
canonicalMilpaFoodSystem =
  traditionalFoodSystem
    "candidate relational milpa food system"
    "situated territory; no universal location asserted"
    "situated community; no spokesperson asserted"
    canonicalFoodSystemStages
    ("maize" ∷ "beans" ∷ "squash" ∷ "chile" ∷ [])
    ("edible greens" ∷ "pollinators" ∷ "soil organisms" ∷ [])
    ("community-retained seed lineages" ∷ [])
    "seasonal and calendrical knowledge remains community-specific"
    "water access and governance remain explicit"
    "soil fertility and reciprocal cultivation remain explicit"
    "ritual relation may exist without being public or exhaustively described"
    "household, market, gift, and reciprocal exchange remain distinct"
    "A milpa is a maintained ecological-social relation, not the sum of crop names."

data KnowledgeTransmissionKind : Set where
  familyTransmission : KnowledgeTransmissionKind
  communityTransmission : KnowledgeTransmissionKind
  apprenticeshipTransmission : KnowledgeTransmissionKind
  marketTransmission : KnowledgeTransmissionKind
  publicationTransmission : KnowledgeTransmissionKind
  institutionalTransmission : KnowledgeTransmissionKind
  commercialTrainingTransmission : KnowledgeTransmissionKind
  namedKnowledgeTransmission : String → KnowledgeTransmissionKind

record KnowledgeTransmission : Set where
  constructor knowledgeTransmission
  field
    teacherOrSource : String
    learnerOrRecipient : String
    transmissionKind : KnowledgeTransmissionKind
    permissionReading : String
    attributionReading : String
    adaptationReading : String

open KnowledgeTransmission public

data LabourContributionKind : Set where
  agriculturalLabour : LabourContributionKind
  ingredientSelectionLabour : LabourContributionKind
  millingGrindingLabour : LabourContributionKind
  fireHeatLabour : LabourContributionKind
  stirringFinishingLabour : LabourContributionKind
  servingCareLabour : LabourContributionKind
  cleaningRecoveryLabour : LabourContributionKind
  teachingLabour : LabourContributionKind
  representationLabour : LabourContributionKind

data ValueFlowKind : Set where
  wageValueFlow : ValueFlowKind
  ownershipValueFlow : ValueFlowKind
  brandValueFlow : ValueFlowKind
  tourismValueFlow : ValueFlowKind
  mediaPrestigeFlow : ValueFlowKind
  institutionalPrestigeFlow : ValueFlowKind
  communityBenefitFlow : ValueFlowKind
  uncompensatedValueFlow : ValueFlowKind

record CulinaryContributionAccount : Set where
  constructor culinaryContributionAccount
  field
    participant : String
    labourContributions : List LabourContributionKind
    knowledgeContributions : List String
    ownershipRights : List String
    compensationReceipts : List String
    attributionReceipts : List String
    decisionRoles : List String
    capturedValueFlows : List ValueFlowKind
    accountReading : String

open CulinaryContributionAccount public

data CulinaryExtraction : Set where
  uncompensatedLabourExtraction : CulinaryExtraction
  unattributedKnowledgeExtraction : CulinaryExtraction
  displacedAuthorshipExtraction : CulinaryExtraction
  symbolicTokenisationExtraction : CulinaryExtraction
  prestigeWithoutBenefitExtraction : CulinaryExtraction
  representationWithoutConsentExtraction : CulinaryExtraction
  heritageBrandCaptureExtraction : CulinaryExtraction
  communityNamePrivateGainExtraction : CulinaryExtraction

record KnowledgeCommercialisation : Set where
  constructor knowledgeCommercialisation
  field
    commercialActor : String
    representedSource : String
    knowledgeDescription : String
    consentStatus : String
    attributionStatus : String
    compensationStatus : String
    controlRights : String
    benefitDistribution : String
    withdrawalRight : String
    possibleExtractions : List CulinaryExtraction

open KnowledgeCommercialisation public

data FoodPowerAxis : Set where
  genderFoodAxis : FoodPowerAxis
  indigeneityFoodAxis : FoodPowerAxis
  raceFoodAxis : FoodPowerAxis
  languageFoodAxis : FoodPowerAxis
  classFoodAxis : FoodPowerAxis
  ruralityFoodAxis : FoodPowerAxis
  migrationFoodAxis : FoodPowerAxis
  ageFoodAxis : FoodPowerAxis
  landTenureFoodAxis : FoodPowerAxis
  restaurantOwnershipFoodAxis : FoodPowerAxis
  credentialFoodAxis : FoodPowerAxis
  mediaAccessFoodAxis : FoodPowerAxis
  colonialityFoodAxis : FoodPowerAxis
  namedFoodPowerAxis : String → FoodPowerAxis

canonicalFoodPowerAxes : List FoodPowerAxis
canonicalFoodPowerAxes =
  genderFoodAxis
  ∷ indigeneityFoodAxis
  ∷ raceFoodAxis
  ∷ languageFoodAxis
  ∷ classFoodAxis
  ∷ ruralityFoodAxis
  ∷ migrationFoodAxis
  ∷ ageFoodAxis
  ∷ landTenureFoodAxis
  ∷ restaurantOwnershipFoodAxis
  ∷ credentialFoodAxis
  ∷ mediaAccessFoodAxis
  ∷ colonialityFoodAxis
  ∷ []

record IntersectionalFoodEffect : Set where
  constructor intersectionalFoodEffect
  field
    participant : String
    axes : List FoodPowerAxis
    opportunityEffects : List String
    burdenEffects : List String
    credibilityEffects : List String
    valueCaptureEffects : List String
    effectReading : String

open IntersectionalFoodEffect public

data HistoricalFoodRelation : Set where
  introducedIngredientRelation : HistoricalFoodRelation
  coercedProductionRelation : HistoricalFoodRelation
  appropriatedTechniqueRelation : HistoricalFoodRelation
  marketAdoptionRelation : HistoricalFoodRelation
  eliteCodificationRelation : HistoricalFoodRelation
  householdAdaptationRelation : HistoricalFoodRelation
  religiousReframingRelation : HistoricalFoodRelation
  nationalCanonisationRelation : HistoricalFoodRelation
  tourismRebrandingRelation : HistoricalFoodRelation
  communityReclamationRelation : HistoricalFoodRelation

data HistoricalMemoryLane : Set where
  IndigenousFoodMemoryLane : HistoricalMemoryLane
  AfroMexicanFoodMemoryLane : HistoricalMemoryLane
  colonialInstitutionLane : HistoricalMemoryLane
  PacificTradeLane : HistoricalMemoryLane
  regionalEcologyLane : HistoricalMemoryLane
  householdMarketLane : HistoricalMemoryLane
  nationalHeritageLane : HistoricalMemoryLane
  diasporaFoodMemoryLane : HistoricalMemoryLane

record HistoricalContribution : Set where
  constructor historicalContribution
  field
    contributorOrCommunity : String
    memoryLane : HistoricalMemoryLane
    relation : HistoricalFoodRelation
    contributionReading : String
    sourceReading : String

open HistoricalContribution public

canonicalAfroMexicanMemoryBoundary : HistoricalContribution
canonicalAfroMexicanMemoryBoundary =
  historicalContribution
    "Afro-Mexican women and communities; no homogeneous spokesperson asserted"
    AfroMexicanFoodMemoryLane
    communityReclamationRelation
    "Afro-Mexican culinary memory, labour, identity, and resistance remain explicit rather than disappearing into an Indigenous-European binary."
    "bounded by Giobanna Buenahora's attributed review and future community-led evidence"

data CommensalRelation : Set where
  ingredientContributionRelation : CommensalRelation
  labourContributionRelation : CommensalRelation
  servingRelation : CommensalRelation
  allocationRelation : CommensalRelation
  reciprocalObligationRelation : CommensalRelation
  exclusionRelation : CommensalRelation
  leftoverDistributionRelation : CommensalRelation

record CommensalDistribution : Set where
  constructor commensalDistribution
  field
    occasion : String
    participants : List String
    relations : List CommensalRelation
    servingOrder : String
    allocationRules : String
    contributionRules : String
    reciprocalDebts : String
    exclusions : List String
    leftoversRoute : String

open CommensalDistribution public

data RepresentationRole : Set where
  practicesRole : RepresentationRole
  knowsRole : RepresentationRole
  teachesRole : RepresentationRole
  representsOwnPracticeRole : RepresentationRole
  representsCommunityRole : RepresentationRole
  speaksForCommunityRole : RepresentationRole
  institutionalSelectorRole : RepresentationRole

record RepresentationAuthority : Set where
  constructor representationAuthority
  field
    actor : String
    role : RepresentationRole
    representedPractice : String
    representedCommunity : String
    occasion : String
    timeScope : String
    authorityEvidence : String
    universalSpokespersonClaim : Bool
    universalSpokespersonClaimIsFalse :
      universalSpokespersonClaim ≡ false

open RepresentationAuthority public

data RelationalPatternGuard : Set where
  noUniversalIndigenousMind : RelationalPatternGuard
  noCrossPeopleIdentity : RelationalPatternGuard
  noContextFreeCulturalEquivalence : RelationalPatternGuard
  noRestrictedKnowledgeInference : RelationalPatternGuard
  noAuthorityFromStructuralAnalogy : RelationalPatternGuard

record RelationalCrossPollination : Set₁ where
  constructor relationalCrossPollination
  field
    sweetgrassAttribution : String
    knotWeaveBridge : Knot.KnotWeaveTopologyCultureBridge
    hyperfabricBridge : Hyper.HyperfabricIntersectionalBodyMemoryBridge
    hyperfabricPowerAxes : List Hyper.PowerAtlasAxis
    hyperfabricPowerAxesAreCanonical :
      hyperfabricPowerAxes ≡ Hyper.canonicalPowerAtlasAxes
    foodPowerAxes : List FoodPowerAxis
    foodPowerAxesAreCanonical : foodPowerAxes ≡ canonicalFoodPowerAxes
    guards : List RelationalPatternGuard
    patternMindUniversalClaim : Bool
    patternMindUniversalClaimIsFalse : patternMindUniversalClaim ≡ false
    culturalIdentityEquivalenceClaim : Bool
    culturalIdentityEquivalenceClaimIsFalse :
      culturalIdentityEquivalenceClaim ≡ false
    crossPollinationReading : String

open RelationalCrossPollination public

canonicalRelationalCrossPollination : RelationalCrossPollination
canonicalRelationalCrossPollination =
  relationalCrossPollination
    Sweetgrass.sweetgrassAttribution
    Knot.canonicalKnotWeaveTopologyCultureBridge
    Hyper.canonicalHyperfabricIntersectionalBodyMemoryBridge
    Hyper.canonicalPowerAtlasAxes
    refl
    canonicalFoodPowerAxes
    refl
    ( noUniversalIndigenousMind
    ∷ noCrossPeopleIdentity
    ∷ noContextFreeCulturalEquivalence
    ∷ noRestrictedKnowledgeInference
    ∷ noAuthorityFromStructuralAnalogy
    ∷ [] )
    false
    refl
    false
    refl
    "Sweetgrass, Sand Talk, weave, braid, and hyperfabric provide attributed bounded comparison lenses. Distinct Zapotec, Wixárika, Purhepecha, Afro-Mexican, Aboriginal Australian, and other worlds remain non-interchangeable."

record TraceablePluralWhole (Part Whole : Set) : Set₁ where
  constructor traceablePluralWhole
  field
    compose : List Part → Whole
    Participates : Part → Whole → Set
    contributionTrace :
      (parts : List Part) →
      (part : Part) →
      Participates part (compose parts) →
      String
    wholeNotReducedToOnePart : Bool
    wholeNotReducedToOnePartIsTrue : wholeNotReducedToOnePart ≡ true

open TraceablePluralWhole public

data MoleWorldSurface : Set where
  materialMoleSurface : MoleWorldSurface
  ecologicalMoleSurface : MoleWorldSurface
  labourMoleSurface : MoleWorldSurface
  commensalMoleSurface : MoleWorldSurface
  textileMoleSurface : MoleWorldSurface
  ritualMoleSurface : MoleWorldSurface
  historicalMoleSurface : MoleWorldSurface
  politicalMoleSurface : MoleWorldSurface
  representationMoleSurface : MoleWorldSurface
  publicationMoleSurface : MoleWorldSurface

record SituatedMoleWorld : Set₁ where
  constructor situatedMoleWorld
  field
    worldLabel : String
    foodSystem : TraditionalFoodSystem
    materialRoute :
      Process.ProcessRoute
        Process.rawComponentAssemblyState
        Process.serviceStableMoleState
    knowledgeTransmissions : List KnowledgeTransmission
    contributionAccounts : List CulinaryContributionAccount
    commercialisations : List KnowledgeCommercialisation
    intersectionalEffects : List IntersectionalFoodEffect
    historicalContributions : List HistoricalContribution
    commensalEvents : List CommensalDistribution
    representationAuthorities : List RepresentationAuthority
    crossPollination : RelationalCrossPollination
    sourceCountReceipt : Sources.canonicalCuisineKnowledgeSourceCount ≡ 22
    projectedDishLabel : String
    completeInverseFromPlateClaim : Bool
    completeInverseFromPlateClaimIsFalse :
      completeInverseFromPlateClaim ≡ false
    worldReading : String

open SituatedMoleWorld public

canonicalSituatedMoleWorld : SituatedMoleWorld
canonicalSituatedMoleWorld =
  situatedMoleWorld
    "candidate situated mole world"
    canonicalMilpaFoodSystem
    Process.canonicalCandidateMoleRoute
    ( knowledgeTransmission
        "community practitioners and named teachers"
        "learner or recipient"
        communityTransmission
        "permission remains source- and community-specific"
        "teachers, communities, and adaptations remain traceable"
        "adaptation does not create authority to speak for the source community"
    ∷ [] )
    ( culinaryContributionAccount
        "collective participant placeholder"
        ( agriculturalLabour
        ∷ ingredientSelectionLabour
        ∷ millingGrindingLabour
        ∷ fireHeatLabour
        ∷ stirringFinishingLabour
        ∷ servingCareLabour
        ∷ cleaningRecoveryLabour
        ∷ teachingLabour
        ∷ [] )
        ("situated culinary knowledge contribution" ∷ [])
        []
        []
        []
        []
        []
        "The empty rights and compensation lists are unresolved obligations, not evidence that no rights or payment exist."
    ∷ [] )
    []
    ( intersectionalFoodEffect
        "situated participant placeholder"
        canonicalFoodPowerAxes
        []
        []
        []
        []
        "Axes are retained for audit; no empirical effect is inferred without evidence."
    ∷ [] )
    (canonicalAfroMexicanMemoryBoundary ∷ [])
    []
    []
    canonicalRelationalCrossPollination
    Sources.canonicalCuisineKnowledgeSourceCountIsTwentyTwo
    "edible mole realisation"
    false
    refl
    "The plate is a projection of ecological, labour, knowledge, commensal, historical, political, and representation relations and cannot reconstruct the complete world by itself."

data SituatedMoleNonCollapse : Set where
  culinarySuccessDoesNotImplySocialJustice : SituatedMoleNonCollapse
  heritageListingDoesNotImplyEthicalRepresentation : SituatedMoleNonCollapse
  IndigenousRepresentationDoesNotImplyIndigenousGovernance : SituatedMoleNonCollapse
  femaleCodedTraditionDoesNotImplyWomenControlValue : SituatedMoleNonCollapse
  publicRecognitionDoesNotImplyCommunityBenefit : SituatedMoleNonCollapse
  celebratedDoesNotImplyCompensated : SituatedMoleNonCollapse
  communityMemberDoesNotImplyCommunitySpokesperson : SituatedMoleNonCollapse
  integrationDoesNotImplyContributionErasure : SituatedMoleNonCollapse
  structuralAnalogyDoesNotImplyCulturalIdentity : SituatedMoleNonCollapse
  heritageProtectionDoesNotImplyFoodSovereignty : SituatedMoleNonCollapse

canonicalSituatedMoleNonCollapses : List SituatedMoleNonCollapse
canonicalSituatedMoleNonCollapses =
  culinarySuccessDoesNotImplySocialJustice
  ∷ heritageListingDoesNotImplyEthicalRepresentation
  ∷ IndigenousRepresentationDoesNotImplyIndigenousGovernance
  ∷ femaleCodedTraditionDoesNotImplyWomenControlValue
  ∷ publicRecognitionDoesNotImplyCommunityBenefit
  ∷ celebratedDoesNotImplyCompensated
  ∷ communityMemberDoesNotImplyCommunitySpokesperson
  ∷ integrationDoesNotImplyContributionErasure
  ∷ structuralAnalogyDoesNotImplyCulturalIdentity
  ∷ heritageProtectionDoesNotImplyFoodSovereignty
  ∷ []

record SituatedMoleWorldBoundary : Set₁ where
  constructor situatedMoleWorldBoundary
  field
    world : SituatedMoleWorld
    nonCollapses : List SituatedMoleNonCollapse
    universalMoleOntologyClaim : Bool
    universalMoleOntologyClaimIsFalse : universalMoleOntologyClaim ≡ false
    historicalClosureClaim : Bool
    historicalClosureClaimIsFalse : historicalClosureClaim ≡ false
    labourJusticeClaim : Bool
    labourJusticeClaimIsFalse : labourJusticeClaim ≡ false
    communityConsentClaim : Bool
    communityConsentClaimIsFalse : communityConsentClaim ≡ false

open SituatedMoleWorldBoundary public

canonicalSituatedMoleWorldBoundary : SituatedMoleWorldBoundary
canonicalSituatedMoleWorldBoundary =
  situatedMoleWorldBoundary
    canonicalSituatedMoleWorld
    canonicalSituatedMoleNonCollapses
    false
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalSituatedMoleWorldReceipt : GenericReceipt.GenericReceipt
canonicalSituatedMoleWorldReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "situated mole world"
    "DASHI.Culture.Cuisine.SituatedMoleWorld"
    "canonicalSituatedMoleWorldBoundary"
    "connects mole process to milpa food systems, labour/value accounts, knowledge transmission, Afro-Mexican memory, commensality, representation, Sweetgrass, weave/braid, and hyperfabric power axes"
    "the bridge does not prove a universal Indigenous mind, cultural equivalence, historical closure, labour justice, community consent, spokesperson authority, or food sovereignty"
    "agda -i . DASHI/Culture/Cuisine/SituatedMoleWorld.agda"
