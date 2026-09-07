module DASHI.Interop.GodsEyeViewActivistThreatAtlasExact where

------------------------------------------------------------------------
-- GOD'S EYE VIEW x PUBLIC-INTEREST ACTIVIST THREAT ATLAS
--
-- This owner cross-pollinates the proof-carrying world residual with existing
-- DASHI crisis/climate, Amalek/Herzog, Zizek, Iran/energy and dashiTRADE lanes.
-- It is deliberately source-bounded: the atlas may organise observations,
-- causal candidates, ideological narratives and action residuals, but it does
-- not turn political theology, activist framing, market movement or a visual
-- world-state rollup into empirical truth or coercive authority.
--
-- CURRENT SOURCE CALIBRATION (accessed 2026-09-08)
--
-- Climate:
--   IPCC AR6 Synthesis Report / WGIII: anthropogenic warming is unequivocal;
--   fossil-fuel combustion is the largest source of CO2 emissions, with land
--   use/agriculture, methane, industrial processes, waste and fluorinated gases
--   remaining material sectors/forcings.
--   https://www.ipcc.ch/report/ar6/syr/
--   https://www.ipcc.ch/report/ar6/wg3/chapter/chapter-1/
--
--   UNEP Emissions Gap Report 2025: current policies remain far from 1.5 C;
--   https://www.unep.org/resources/emissions-gap-report-2025
--
--   United Nations methane issue page: methane is the second-largest cause of
--   warming after CO2; major anthropogenic sectors are agriculture, fossil
--   fuels and waste.
--   https://www.un.org/en/climatechange/science/climate-issues/methane
--
-- Political theology / Christian nationalism / Christian Zionism:
--   Nilay Saiya, "The varieties of American Christian nationalism",
--   Politics and Religion (2025), DOI 10.1017/S1755048325000069.
--   The source documents Trump-as-messianic/Cyrus rhetoric in some charismatic
--   dominionist circles; it does NOT establish a supernatural identity.
--
--   Sean Durbin, "Christian Zionism in the United States, 1930-2020",
--   Oxford Research Encyclopedia of Religion (2023),
--   DOI 10.1093/acrefore/9780199340378.013.1205.
--   This supports an eschatology/foreign-policy relationship in parts of
--   Christian Zionism, not a single motive for all evangelicals or Israelis.
--
--   Motti Inbari and Kirill Bumin, Christian Zionism in the Twenty-First
--   Century, OUP (2023/2024), DOI 10.1093/oso/9780197649305.001.0001.
--   Their survey work explicitly shows theological and demographic plurality.
--
-- Repo source boundaries remain authoritative for Amalek, Herzog, Zizek, Iran,
-- climate-conflict comparison, market/statistical and dashiTRADE semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.GodsEyeViewPublicInterestWorldResidualExact as Public
import DASHI.Governance.ComparativeCrisisClimateAtlas as Crisis
import DASHI.Governance.AmalekProvenanceRoleBinding as Amalek
import DASHI.Law.HerzogFascismAntifascistAmalekCrossPollinationExact as Herzog
import DASHI.Reasoning.ZizekPNFSourceAtlas as Zizek
import DASHI.Governance.TrumpEnergyCrackSpreadCrossPollinationExact as Energy
import DASHI.Finance.DashiTradeFibreBridgeExact as DashiTrade
import DASHI.Finance.DeepStatArbFibrePipelineExact as Statistics
import DASHI.Economics.MarketTransitionGrammarCyberneticsExact as Market

------------------------------------------------------------------------
-- 1. Public-interest case families are not one equivalence class.
------------------------------------------------------------------------

data ActivistCaseKind : Set where
  climateEmissionsCase : ActivistCaseKind
  fossilFuelInfrastructureCase : ActivistCaseKind
  methaneSuperEmitterCase : ActivistCaseKind
  landLossDeforestationCase : ActivistCaseKind
  illegalExtractionMiningCase : ActivistCaseKind
  dataCentreResourceConflictCase : ActivistCaseKind
  detentionRemovalCarceralCase : ActivistCaseKind
  borderMilitarisationCase : ActivistCaseKind
  warCivilianProtectionCase : ActivistCaseKind
  institutionalViolenceCase : ActivistCaseKind
  corruptionCaptureCase : ActivistCaseKind
  informationManipulationCase : ActivistCaseKind
  politicalTheologyMobilisationCase : ActivistCaseKind
  marketExternalityCase : ActivistCaseKind
  namedActivistCase : String → ActivistCaseKind

record ActivistCase : Set where
  constructor activist-case
  field
    caseKind : ActivistCaseKind
    caseReference : String
    affectedPopulationOrEcologyReference : String
    observedPowerHolderReference : String
    publicInterestReference : String
    evidenceGraphReference : String
    coverageReference : String
    uncertaintyReference : String
    legalOrNormativeReference : String
    safePublicationReference : String

open ActivistCase public

------------------------------------------------------------------------
-- 2. UN/IPCC-calibrated climate driver surface.
--
-- "Top threat" is not represented as a timeless ordinal leaderboard.  The
-- sources instead support material driver families and sector contributions.
------------------------------------------------------------------------

data ClimateDriver : Set where
  fossilFuelCombustionCO2 : ClimateDriver
  fossilFuelMethane : ClimateDriver
  agricultureMethaneNitrousOxide : ClimateDriver
  landUseAndDeforestation : ClimateDriver
  industrialProcessEmissions : ClimateDriver
  wasteAndWastewaterMethane : ClimateDriver
  fluorinatedGases : ClimateDriver
  unsustainableConsumptionProduction : ClimateDriver

canonicalClimateDrivers : List ClimateDriver
canonicalClimateDrivers =
  fossilFuelCombustionCO2
  ∷ fossilFuelMethane
  ∷ agricultureMethaneNitrousOxide
  ∷ landUseAndDeforestation
  ∷ industrialProcessEmissions
  ∷ wasteAndWastewaterMethane
  ∷ fluorinatedGases
  ∷ unsustainableConsumptionProduction
  ∷ []

record ClimateDriverReceipt : Set where
  constructor climate-driver-receipt
  field
    driver : ClimateDriver
    authority : String
    sourceReference : String
    boundedClaim : String
    measurementOrAssessmentReference : String
    currentObservationRequiredForLocalAttribution : Bool

open ClimateDriverReceipt public

fossilCombustionReceipt : ClimateDriverReceipt
fossilCombustionReceipt =
  climate-driver-receipt
    fossilFuelCombustionCO2
    "IPCC AR6 WGIII"
    "AR6 WGIII Chapter 1 FAQ 1.2"
    "fossil-fuel combustion is the largest source of anthropogenic CO2 emissions; this does not identify the cause of an individual local plume"
    "IPCC sector emissions assessment"
    true

methaneReceipt : ClimateDriverReceipt
methaneReceipt =
  climate-driver-receipt
    fossilFuelMethane
    "United Nations climate issue page / UNEP methane programme"
    "Methane: From Super Pollutant to Climate Solution"
    "methane is a major near-term warming driver and fossil fuels are a major anthropogenic methane sector; local attribution remains observation-specific"
    "satellite/inventory/source-specific methane measurement"
    true

landUseReceipt : ClimateDriverReceipt
landUseReceipt =
  climate-driver-receipt
    landUseAndDeforestation
    "IPCC AR6"
    "AR6 WGIII AFOLU / AR6 Synthesis Report"
    "land-use change, agriculture and deforestation materially contribute to greenhouse-gas emissions and climate risk"
    "land-cover, carbon-flux and activity-data assessment"
    true

------------------------------------------------------------------------
-- 3. Climate activism follows the same observation least-privilege path.
------------------------------------------------------------------------

record ClimateAccountabilityResidual : Set where
  constructor climate-accountability-residual
  field
    case : ActivistCase
    worldResidual : Public.WorldQueryResidual
    candidateDrivers : List ClimateDriver
    emissionsObservationReference : String
    historicalBaselineReference : String
    ownershipOrOperatorReference : String
    regulatoryObligationReference : String
    harmedInterestReference : String
    missingCausalPrerequisiteReference : String
    mitigationOrRemedyReference : String

open ClimateAccountabilityResidual public

------------------------------------------------------------------------
-- 4. Infrastructure/extraction/resource cases preserve incidence.
------------------------------------------------------------------------

data ResourceBurden : Set where
  electricityBurden : ResourceBurden
  waterBurden : ResourceBurden
  landBurden : ResourceBurden
  housingBurden : ResourceBurden
  habitatBurden : ResourceBurden
  toxicPollutionBurden : ResourceBurden
  carbonBurden : ResourceBurden
  labourBurden : ResourceBurden
  indigenousCountryBurden : ResourceBurden
  displacementBurden : ResourceBurden

record InfrastructureBurdenFibre : Set where
  constructor infrastructure-burden-fibre
  field
    case : ActivistCase
    burdens : List ResourceBurden
    beneficiaryReference : String
    burdenBearerReference : String
    ownershipReference : String
    permitOrAuthorityReference : String
    consultationConsentReference : String
    externalityReference : String
    temporalReference : String
    remedyReference : String

open InfrastructureBurdenFibre public

------------------------------------------------------------------------
-- 5. Detention, border and coercive-state cases require protection against
-- activist tooling becoming a targeting database.
------------------------------------------------------------------------

data PublicationSensitivity : Set where
  publicInstitutionalFact : PublicationSensitivity
  publicFacilityFact : PublicationSensitivity
  aggregatePopulationFact : PublicationSensitivity
  sensitiveIndividualFact : PublicationSensitivity
  vulnerablePersonLocation : PublicationSensitivity
  protectedWitnessOrSource : PublicationSensitivity

record ActivistPublicationGate : Set where
  constructor activist-publication-gate
  field
    case : ActivistCase
    sensitivity : PublicationSensitivity
    publicInterestReference : String
    necessityReference : String
    minimisationReference : String
    redactionAggregationReference : String
    retaliationRiskReference : String
    informedConsentReference : String
    publicationAuthorityReference : String
    downstreamTargetingBlockedReference : String

open ActivistPublicationGate public

------------------------------------------------------------------------
-- 6. Political theology is an interpretive/rhetorical observation fibre.
------------------------------------------------------------------------

data PoliticalTheologyNarrative : Set where
  trumpAsCyrusNarrative : PoliticalTheologyNarrative
  trumpAsMessianicNarrative : PoliticalTheologyNarrative
  trumpAsAntichristNarrative : PoliticalTheologyNarrative
  endTimesNarrative : PoliticalTheologyNarrative
  christianZionistProphecyNarrative : PoliticalTheologyNarrative
  amalekRoleBindingNarrative : PoliticalTheologyNarrative
  islamicEschatologyNarrative : PoliticalTheologyNarrative
  secularApocalypticNarrative : PoliticalTheologyNarrative
  namedPoliticalTheologyNarrative : String → PoliticalTheologyNarrative

-- These statuses classify evidence ABOUT a narrative; none promotes the
-- narrative's supernatural content to world-state truth.
data NarrativeEvidenceStatus : Set where
  documentedSpeakerUtterance : NarrativeEvidenceStatus
  documentedMovementBelief : NarrativeEvidenceStatus
  scholarlyInterpretation : NarrativeEvidenceStatus
  contestedInterpretation : NarrativeEvidenceStatus
  unsupportedAsEmpiricalFact : NarrativeEvidenceStatus

record PoliticalTheologyReceipt : Set where
  constructor political-theology-receipt
  field
    narrative : PoliticalTheologyNarrative
    status : NarrativeEvidenceStatus
    speakerOrCommunityReference : String
    sourceReference : String
    exactClaimReference : String
    historicalContextReference : String
    policyLinkReference : String
    causalTransportEvidenceReference : String
    supernaturalTruthClaimedByDASHI : Bool

open PoliticalTheologyReceipt public

trumpCyrusScholarshipReceipt : PoliticalTheologyReceipt
trumpCyrusScholarshipReceipt =
  political-theology-receipt
    trumpAsCyrusNarrative
    documentedMovementBelief
    "selected charismatic dominionist / evangelical circles"
    "Saiya 2025, Politics and Religion, DOI 10.1017/S1755048325000069; Hughes et al. 2025, Christian America and the Kingdom of God"
    "Trump has been framed by some supporters through a Cyrus/messianic analogy"
    "American Christian nationalism and charismatic dominionism"
    "possible legitimation/mobilisation relationship; policy effect must be separately established"
    "no unique causal transport inferred from narrative presence"
    false

christianZionismEschatologyReceipt : PoliticalTheologyReceipt
christianZionismEschatologyReceipt =
  political-theology-receipt
    christianZionistProphecyNarrative
    scholarlyInterpretation
    "parts of the American Christian Zionist movement"
    "Durbin 2023 DOI 10.1093/acrefore/9780199340378.013.1205; Inbari and Bumin 2023 DOI 10.1093/oso/9780197649305.001.0001"
    "eschatological beliefs can form one component of Christian-Zionist support for Israel, with substantial internal variation"
    "US evangelical religion, Christian Zionism, Israel and foreign-policy politics"
    "policy association is empirical and heterogeneous"
    "no Netanyahu-to-Trump or end-times causal chain inferred without separate evidence"
    false

trumpAntichristReceipt : PoliticalTheologyReceipt
trumpAntichristReceipt =
  political-theology-receipt
    trumpAsAntichristNarrative
    contestedInterpretation
    "commentators/theological interpreters who use Antichrist language"
    "interpretive claim requiring speaker-specific source; not established by the Christian-nationalism literature as a supernatural fact"
    "Trump is compared by some interpreters with biblical Antichrist motifs"
    "Christian apocalyptic interpretation and contemporary political rhetoric"
    "may be studied as rhetoric, reception or political theology"
    "no empirical or supernatural identity transport"
    false

------------------------------------------------------------------------
-- 7. No person/population may be classified by a supernatural role merely from
-- political conduct, identity, ethnicity, religion or narrative association.
------------------------------------------------------------------------

data PoliticalConductProvesAntichristIdentity : Set where

politicalConductDoesNotProveAntichristIdentity :
  PoliticalConductProvesAntichristIdentity → ⊥
politicalConductDoesNotProveAntichristIdentity ()


data ReligiousIdentityProvesEnemyRole : Set where

religiousIdentityDoesNotProveEnemyRole : ReligiousIdentityProvesEnemyRole → ⊥
religiousIdentityDoesNotProveEnemyRole ()

------------------------------------------------------------------------
-- 8. Existing Amalek/Herzog boundaries are inherited, not weakened.
------------------------------------------------------------------------

amalekBoundary : Amalek.AmalekBoundary
amalekBoundary = Amalek.canonicalAmalekBoundary

herzogAmalekBoundary : Herzog.GenocideAmalekBoundary
herzogAmalekBoundary = Herzog.canonicalGenocideAmalekBoundary

amalekRoleDoesNotEqualIdentity :
  Amalek.roleBindingEqualsIdentity amalekBoundary ≡ false
amalekRoleDoesNotEqualIdentity = refl

amalekCommandNeedsSeparateEvidence :
  Amalek.commandTransportRequiresSeparateEvidence amalekBoundary ≡ true
amalekCommandNeedsSeparateEvidence = refl

------------------------------------------------------------------------
-- 9. Zizek is an ideology/parallax calibration lane, not motive authority.
------------------------------------------------------------------------

zizekSources : Zizek.Source.AttributedSourceAtlas
zizekSources = Zizek.zizekPNFSourceAtlas

record IdeologyAudit : Set where
  constructor ideology-audit
  field
    narrativeReference : String
    materialInterestReference : String
    institutionalReproductionReference : String
    contradictionOrParallaxReference : String
    surplusOrExternalityReference : String
    affectedGroupReference : String
    sourceEvidenceReference : String
    ideologyReadingDeterminesActorMotive : Bool

open IdeologyAudit public

------------------------------------------------------------------------
-- 10. Market and dashiTRADE lanes can consume public-interest observations,
-- but activism, market inference and trading permission remain different uses.
------------------------------------------------------------------------

energyBoundary : Energy.TrumpEnergyCrackSpreadBoundary
energyBoundary = Energy.canonicalTrumpEnergyCrackSpreadBoundary

statisticsBoundary : Statistics.SharpeAuthorityBoundary
statisticsBoundary = Statistics.canonicalSharpeAuthorityBoundary

dashiTradeBoundary : DashiTrade.ResidualToTradeAuthorityBoundary
dashiTradeBoundary = DashiTrade.canonicalResidualToTradeAuthorityBoundary

marketBoundary : Market.MarketTransitionGrammarBoundary
marketBoundary = Market.canonicalMarketTransitionGrammarBoundary

record ActivismMarketSeparation : Set where
  constructor activism-market-separation
  field
    publicInterestObservationReference : String
    marketSignalReference : String
    statisticalValidationReference : String
    tradeProposalReference : String
    permissionReference : String
    activistFindingCreatesTradePermission : Bool
    marketProfitCreatesMoralAuthority : Bool
    profitableTradeProvesActivistClaimTrue : Bool

open ActivismMarketSeparation public

canonicalActivismMarketSeparation : ActivismMarketSeparation
canonicalActivismMarketSeparation =
  activism-market-separation
    "public-interest evidence graph"
    "optional market-impact projection"
    "separate point-in-time statistical validation"
    "separate dashiTRADE proposal"
    "separate permission/actionability kernel"
    false false false

------------------------------------------------------------------------
-- 11. Activist proof search: concern -> proposition -> evidence residual ->
-- least-intrusive observation -> publication/remedy; not concern -> target.
------------------------------------------------------------------------

record ActivistProofSearchRoute : Set where
  constructor activist-proof-search-route
  field
    case : ActivistCase
    concernReference : String
    propositionReference : String
    currentEvidenceReference : String
    contradictionReference : String
    missingPrerequisiteReference : String
    worldResidual : Public.WorldQueryResidual
    observationAdmission : Public.ObservationLeastPrivilegeAdmission
    publicationGateReference : String
    remedyOrAccountabilityReference : String
    targetSelectionFromIdentityAlone : Bool

open ActivistProofSearchRoute public

------------------------------------------------------------------------
-- 12. Crisis/climate atlas anchor keeps comparative cases non-equated.
------------------------------------------------------------------------

crisisBoundary : Crisis.ComparativeCrisisClimateAtlasBoundary
crisisBoundary = Crisis.canonicalComparativeCrisisClimateAtlasBoundary

climateNotSoleCause :
  Crisis.climateDoesNotActAsSoleCause crisisBoundary
  ≡ refl
climateNotSoleCause = refl

------------------------------------------------------------------------
-- 13. Canonical public-interest threat-atlas boundary.
------------------------------------------------------------------------

record ActivistThreatAtlasBoundary : Set where
  constructor activist-threat-atlas-boundary
  field
    climateDriverListIsLocalCausalFinding : Bool
    climateDriverListIsLocalCausalFindingIsFalse : climateDriverListIsLocalCausalFinding ≡ false

    activistConcernCreatesTargetingAuthority : Bool
    activistConcernCreatesTargetingAuthorityIsFalse : activistConcernCreatesTargetingAuthority ≡ false

    vulnerablePersonLocationShouldBeMaximallyExposed : Bool
    vulnerablePersonLocationShouldBeMaximallyExposedIsFalse : vulnerablePersonLocationShouldBeMaximallyExposed ≡ false

    politicalTheologyNarrativeIsSupernaturalFact : Bool
    politicalTheologyNarrativeIsSupernaturalFactIsFalse : politicalTheologyNarrativeIsSupernaturalFact ≡ false

    trumpCanBeFormallyProvedAntichristFromPoliticalEvidence : Bool
    trumpCanBeFormallyProvedAntichristFromPoliticalEvidenceIsFalse : trumpCanBeFormallyProvedAntichristFromPoliticalEvidence ≡ false

    christianZionismIsSingleUniformEndTimesDoctrine : Bool
    christianZionismIsSingleUniformEndTimesDoctrineIsFalse : christianZionismIsSingleUniformEndTimesDoctrine ≡ false

    islamMayBeCollapsedToSinglePoliticalActor : Bool
    islamMayBeCollapsedToSinglePoliticalActorIsFalse : islamMayBeCollapsedToSinglePoliticalActor ≡ false

    amalekRoleBindingCreatesPopulationIdentity : Bool
    amalekRoleBindingCreatesPopulationIdentityIsFalse : amalekRoleBindingCreatesPopulationIdentity ≡ false

    climatePressureErasesPoliticalResponsibility : Bool
    climatePressureErasesPoliticalResponsibilityIsFalse : climatePressureErasesPoliticalResponsibility ≡ false

    marketProfitCreatesPublicInterestAuthority : Bool
    marketProfitCreatesPublicInterestAuthorityIsFalse : marketProfitCreatesPublicInterestAuthority ≡ false

    publicInterestObservationMustPreserveContestability : Bool
    publicInterestObservationMustPreserveContestabilityIsTrue : publicInterestObservationMustPreserveContestability ≡ true

    powerHolderAccountabilityAndVulnerablePersonExposureAreDistinct : Bool
    powerHolderAccountabilityAndVulnerablePersonExposureAreDistinctIsTrue : powerHolderAccountabilityAndVulnerablePersonExposureAreDistinct ≡ true

canonicalActivistThreatAtlasBoundary : ActivistThreatAtlasBoundary
canonicalActivistThreatAtlasBoundary =
  activist-threat-atlas-boundary
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
    true refl
    true refl
