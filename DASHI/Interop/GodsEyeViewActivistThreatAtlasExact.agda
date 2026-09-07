module DASHI.Interop.GodsEyeViewActivistThreatAtlasExact where

------------------------------------------------------------------------
-- GOD'S EYE VIEW x PUBLIC-INTEREST ACTIVIST THREAT ATLAS
--
-- Purpose: organise evidence-led public-interest investigations across climate,
-- extraction/infrastructure, detention/border, war/civilian-protection,
-- information-integrity and political-theology cases without turning an
-- activist concern, ideology reading, market signal, religious role or map
-- visibility into empirical truth, targeting authority or coercive authority.
--
-- SOURCE CALIBRATION (accessed 2026-09-08)
-- Climate: IPCC AR6 Synthesis/WGIII; UNEP Emissions Gap Report 2025; UN/UNEP
-- methane material.  These support driver families, not a timeless ordinal
-- "top threats" leaderboard and not local source attribution without local
-- observations.
--
-- Political theology: Nilay Saiya, "The varieties of American Christian
-- nationalism", Politics and Religion (2025), DOI 10.1017/S1755048325000069;
-- Sean Durbin, "Christian Zionism in the United States, 1930-2020" (2023),
-- DOI 10.1093/acrefore/9780199340378.013.1205; Motti Inbari and Kirill Bumin,
-- Christian Zionism in the Twenty-First Century, OUP,
-- DOI 10.1093/oso/9780197649305.001.0001.  These calibrate documented rhetoric,
-- movement belief and scholarly interpretation.  DASHI makes no supernatural
-- truth claim from them.
--
-- Existing DASHI Amalek/Herzog, comparative crisis/climate, Zizek, Iran/energy,
-- market/statistical and dashiTRADE owners remain separate authority fibres.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.GodsEyeViewPublicInterestWorldResidualExact as Public
import DASHI.Governance.ComparativeCrisisClimateAtlas
import DASHI.Governance.AmalekProvenanceRoleBinding
import DASHI.Law.HerzogFascismAntifascistAmalekCrossPollinationExact
import DASHI.Reasoning.ZizekPNFSourceAtlas
import DASHI.Governance.TrumpEnergyCrackSpreadCrossPollinationExact
import DASHI.Finance.DashiTradeFibreBridgeExact
import DASHI.Finance.DeepStatArbFibrePipelineExact
import DASHI.Economics.MarketTransitionGrammarCyberneticsExact

------------------------------------------------------------------------
-- 1. Case families.  Named cases remain containers until separately sourced.
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
-- 2. Source-backed climate driver families.
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
    authorityReference : String
    sourceReference : String
    boundedClaim : String
    localAttributionReference : String
    localAttributionStillRequired : Bool

fossilCombustionReceipt : ClimateDriverReceipt
fossilCombustionReceipt =
  climate-driver-receipt
    fossilFuelCombustionCO2
    "IPCC AR6 WGIII"
    "AR6 WGIII Chapter 1 / synthesis"
    "fossil-fuel combustion is the largest source of anthropogenic CO2 emissions"
    "a global/sector assessment does not identify the cause of an individual local observation"
    true

methaneReceipt : ClimateDriverReceipt
methaneReceipt =
  climate-driver-receipt
    fossilFuelMethane
    "United Nations / UNEP methane programme"
    "UN climate methane issue material"
    "methane is a major near-term warming driver; fossil fuels are one major anthropogenic sector"
    "facility or event attribution requires source-specific observation"
    true

------------------------------------------------------------------------
-- 3. Climate accountability is a residual, not accusation-by-category.
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

------------------------------------------------------------------------
-- 4. Infrastructure/extraction/resource cases preserve who benefits and who
-- bears the burden instead of flattening everything to one environmental score.
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

------------------------------------------------------------------------
-- 5. Publication safety: an accountability tool must not become a targeting
-- database for migrants, detainees, witnesses, activists or other vulnerable
-- people.
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
    consentOrProtectiveBasisReference : String
    publicationAuthorityReference : String
    downstreamTargetingBlockedReference : String

------------------------------------------------------------------------
-- 6. Political theology is evidence ABOUT narratives and mobilisation.
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

trumpCyrusScholarshipReceipt : PoliticalTheologyReceipt
trumpCyrusScholarshipReceipt =
  political-theology-receipt
    trumpAsCyrusNarrative
    documentedMovementBelief
    "selected charismatic dominionist / evangelical circles"
    "Saiya 2025 DOI 10.1017/S1755048325000069"
    "some supporters frame Trump through Cyrus or messianic analogy"
    "American Christian nationalism / charismatic dominionism"
    "possible rhetoric, legitimation or mobilisation link; policy effect requires separate evidence"
    "no unique causal transport inferred from narrative presence"
    false

christianZionismEschatologyReceipt : PoliticalTheologyReceipt
christianZionismEschatologyReceipt =
  political-theology-receipt
    christianZionistProphecyNarrative
    scholarlyInterpretation
    "parts of American Christian Zionism"
    "Durbin 2023 DOI 10.1093/acrefore/9780199340378.013.1205; Inbari/Bumin DOI 10.1093/oso/9780197649305.001.0001"
    "eschatological belief can be one strand of Christian-Zionist support for Israel, with substantial internal variation"
    "US evangelical religion, Israel and foreign-policy politics"
    "policy association is empirical and heterogeneous"
    "no Netanyahu-to-Trump or end-times causal chain inferred without separate evidence"
    false

trumpAntichristReceipt : PoliticalTheologyReceipt
trumpAntichristReceipt =
  political-theology-receipt
    trumpAsAntichristNarrative
    contestedInterpretation
    "speaker-specific commentators or theological interpreters"
    "interpretive source required per speaker; not established as supernatural fact by the cited scholarship"
    "Trump may be compared with biblical Antichrist motifs as political theology or rhetoric"
    "Christian apocalyptic interpretation and contemporary politics"
    "possible reception/mobilisation effect must be separately evidenced"
    "no empirical or supernatural identity transport"
    false

------------------------------------------------------------------------
-- 7. Sacred enemy roles cannot be inferred from political/religious identity.
------------------------------------------------------------------------

data PoliticalConductProvesAntichristIdentity : Set where
politicalConductDoesNotProveAntichristIdentity :
  PoliticalConductProvesAntichristIdentity → ⊥
politicalConductDoesNotProveAntichristIdentity ()

data ReligiousIdentityProvesEnemyRole : Set where
religiousIdentityDoesNotProveEnemyRole : ReligiousIdentityProvesEnemyRole → ⊥
religiousIdentityDoesNotProveEnemyRole ()

------------------------------------------------------------------------
-- 8. Zizek/parallax-style ideology audit stays interpretive: an ideological
-- reading can expose contradiction/surplus/institutional reproduction without
-- becoming privileged access to an actor's motive.
------------------------------------------------------------------------

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

canonicalIdeologyNonAuthority : IdeologyAudit
canonicalIdeologyNonAuthority =
  ideology-audit
    "interpretive narrative"
    "material-interest evidence kept separately"
    "institutional-reproduction evidence kept separately"
    "parallax/contradiction reading"
    "surplus/externality reading"
    "affected group remains explicitly situated"
    "attributed source receipts remain required"
    false

------------------------------------------------------------------------
-- 9. Activism, market inference and dashiTRADE permission are different uses.
------------------------------------------------------------------------

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
-- 10. Activist proof search: concern -> proposition -> evidence residual ->
-- least-intrusive observation -> publication/remedy; never concern -> target.
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

------------------------------------------------------------------------
-- 11. Canonical boundary.
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
