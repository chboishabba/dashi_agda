module DASHI.Interop.GodsEyeViewMarketAgroecologyInternationalAccountabilityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Interop.GodsEyeViewPublicInterestWorldResidualExact as Public
import DASHI.Interop.GodsEyeViewDiagnosisDrivenActivistRollupExact as Diagnosis
import DASHI.Finance.DeepStatArbFibrePipelineExact as StatArb
import DASHI.Finance.DashiTradeFibreBridgeExact as DashiTrade
import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as LES
import DASHI.Cognition.PNF.SensibLawTerraNulliusTwoEyedSystemContinuityExact as TwoEyed
import DASHI.Reasoning.ZizekPNFSourceAtlas as Zizek

------------------------------------------------------------------------
-- PUBLIC-INTEREST MARKET ABUSE / AGROECOLOGY / INTERNATIONAL ACCOUNTABILITY
--
-- Source-attribution boundary:
--   * Kalshi/CFTC primary material establishes market-data and enforcement
--     surfaces, not guilt of any unnamed trader.
--   * NASA/FAO and peer-reviewed remote-sensing sources establish observation
--     capabilities, not authority to impose agricultural interventions.
--   * UN statements/resolutions establish institutional legal/political views
--     and Charter propositions; DASHI does not silently promote them into a
--     court judgment on individual responsibility.
--   * Two-Eyed Seeing/Mabo/LES owners preserve distinct knowledge and authority
--     strands; satellite precision does not erase community authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Prediction-market/on-chain anomaly detection is evidence production,
-- never an insider-trading verdict by itself.
------------------------------------------------------------------------

data MarketAbuseHypothesis : Set where
  informedTrading : MarketAbuseHypothesis
  directOutcomeInfluence : MarketAbuseHypothesis
  marketManipulation : MarketAbuseHypothesis
  coordinatedTrading : MarketAbuseHypothesis
  washOrSelfTrading : MarketAbuseHypothesis
  publicInformationSkill : MarketAbuseHypothesis
  liquidityOrMicrostructureEffect : MarketAbuseHypothesis
  coincidence : MarketAbuseHypothesis
  unresolvedMarketMechanism : MarketAbuseHypothesis

record PredictionMarketObservation : Set where
  constructor prediction-market-observation
  field
    venueReference : String
    marketTickerOrContractReference : String
    publicTradeDataReference : String
    orderbookOrLiquidityReference : String
    eventTimeReference : String
    informationReleaseTimeReference : String
    abnormalTimingReference : String
    abnormalReturnOrWinRateReference : String
    sizeConcentrationReference : String
    relatedAccountOrWalletReference : String
    publicInformationSetReference : String
    candidateHypotheses : List MarketAbuseHypothesis
    firstMissingPrerequisiteReference : String

record MarketAbuseResidual : Set where
  constructor market-abuse-residual
  field
    observation : PredictionMarketObservation
    diagnosedConcernReference : String
    materialNonpublicInformationReference : String
    dutyTrustOrInfluenceReference : String
    identityAttributionReference : String
    walletEntityResolutionReference : String
    crossVenueLinkageReference : String
    sourceOfFundsReference : String
    communicationsOrEmploymentReference : String
    alternativeExplanationReference : String
    legalStandardReference : String
    leastIntrusiveHighestAlphaNextObservationReference : String

record KalshiPrimaryPacket : Set where
  constructor kalshi-primary-packet
  field
    apiReference : String
    cftcReference : String
    exchangePolicyReference : String
    publicTradesExposeIdentity : Bool
    publicTradesExposeIdentityIsFalse : publicTradesExposeIdentity ≡ false
    anomalyEqualsInsiderTradingFinding : Bool
    anomalyEqualsInsiderTradingFindingIsFalse : anomalyEqualsInsiderTradingFinding ≡ false
    influenceAndNonpublicInformationNeedSeparateEvidence : Bool
    influenceAndNonpublicInformationNeedSeparateEvidenceIsTrue : influenceAndNonpublicInformationNeedSeparateEvidence ≡ true

kalshiPrimaryPacket : KalshiPrimaryPacket
kalshiPrimaryPacket = kalshi-primary-packet
  "Kalshi Trade API v2: GET /markets/trades and /historical/trades expose ticker, price, quantity, side and timestamp; orderbook endpoint exposes price levels/size"
  "CFTC Release 9185-26, 2026-02-25: prediction-market advisory following cases involving misuse of nonpublic information/fraud on KalshiEX"
  "Kalshi insider-trading policy: real-time anomaly screening, conflict/influence restrictions and investigation/enforcement process"
  false refl false refl true refl

record InformedTradingResearchPacket : Set where
  constructor informed-trading-research-packet
  field
    sourceReference : String
    boundedClaimReference : String
    caseStudyEvidenceCreatesLegalFinding : Bool
    caseStudyEvidenceCreatesLegalFindingIsFalse : caseStudyEvidenceCreatesLegalFinding ≡ false

mittsOfir2026Packet : InformedTradingResearchPacket
mittsOfir2026Packet = informed-trading-research-packet
  "Joshua Mitts & Moran Ofir, From Iran to Taylor Swift: Informed Trading in Prediction Markets, Columbia Law and Economics Working Paper, 2026"
  "systematic empirical/legal study reports case studies of apparently informed trading on Polymarket and Kalshi; attribution/legal liability remains case-specific"
  false refl

------------------------------------------------------------------------
-- 2. dashiTRADE/SOLFUNMEME separation.
--
-- The same anomaly may be useful to an accountability consumer and separately
-- to a market consumer.  Public-interest suspicion does not create trade
-- permission, and profitable trading does not validate an accusation.
------------------------------------------------------------------------

record AccountabilityTradeSeparation : Set where
  constructor accountability-trade-separation
  field
    marketAbuseResidualReference : String
    statisticalValidationReference : String
    dashiTradeFibreReference : String
    permissionReference : String
    publicInterestFindingCreatesTradePermission : Bool
    publicInterestFindingCreatesTradePermissionIsFalse : publicInterestFindingCreatesTradePermission ≡ false
    profitableTradeProvesInsiderTrading : Bool
    profitableTradeProvesInsiderTradingIsFalse : profitableTradeProvesInsiderTrading ≡ false
    tokenOrProofRewardCreatesEpistemicTruth : Bool
    tokenOrProofRewardCreatesEpistemicTruthIsFalse : tokenOrProofRewardCreatesEpistemicTruth ≡ false

canonicalAccountabilityTradeSeparation : AccountabilityTradeSeparation
canonicalAccountabilityTradeSeparation = accountability-trade-separation
  "prediction/on-chain market abuse residual"
  StatArb.pipelineBoundaryStatement
  DashiTrade.bridgeBoundaryStatement
  "existing dashiTRADE permission/actionability kernels remain authoritative"
  false refl false refl false refl

zizekSourceBoundaryReference : String
zizekSourceBoundaryReference =
  "SOLFUNMEME/JMD source material remains attributed through DASHI.Reasoning.ZizekPNFSourceAtlas; token/economic feedback is not source or theorem authority"

------------------------------------------------------------------------
-- 3. LES world-scale agroecology observation.
------------------------------------------------------------------------

data AgroecologyObservationCoordinate : Set where
  canopyVigour : AgroecologyObservationCoordinate
  evapotranspiration : AgroecologyObservationCoordinate
  soilMoistureProxy : AgroecologyObservationCoordinate
  cropWaterStress : AgroecologyObservationCoordinate
  pestDiseaseStress : AgroecologyObservationCoordinate
  nutrientStress : AgroecologyObservationCoordinate
  yieldEstimate : AgroecologyObservationCoordinate
  phenology : AgroecologyObservationCoordinate
  canopyStructure : AgroecologyObservationCoordinate
  biodiversityHabitatStructure : AgroecologyObservationCoordinate
  erosionBareGround : AgroecologyObservationCoordinate
  fireFloodDroughtDamage : AgroecologyObservationCoordinate
  orchardTreeHealth : AgroecologyObservationCoordinate
  agroforestryHeterogeneity : AgroecologyObservationCoordinate

record AgroecologyObservationPacket : Set where
  constructor agroecology-observation-packet
  field
    farmOrCountryReference : String
    coordinates : List AgroecologyObservationCoordinate
    satelliteReference : String
    aerialDroneReference : String
    fieldObservationReference : String
    temporalBaselineReference : String
    modelCalibrationReference : String
    uncertaintyReference : String
    localKnowledgeReference : String
    landCountryAuthorityReference : String
    interventionAuthorityReference : String
    observationCreatesPrescriptionAuthority : Bool
    observationCreatesPrescriptionAuthorityIsFalse : observationCreatesPrescriptionAuthority ≡ false

broadacrePermaculturePacket : AgroecologyObservationPacket
broadacrePermaculturePacket = agroecology-observation-packet
  "LES broadacre/permaculture/orchard/agroforestry situated planning surface"
  (canopyVigour ∷ evapotranspiration ∷ soilMoistureProxy ∷ cropWaterStress ∷ pestDiseaseStress ∷ nutrientStress ∷ yieldEstimate ∷ phenology ∷ canopyStructure ∷ biodiversityHabitatStructure ∷ erosionBareGround ∷ fireFloodDroughtDamage ∷ orchardTreeHealth ∷ agroforestryHeterogeneity ∷ [])
  "NASA/USGS Landsat, ESA Copernicus Sentinel-1/2, and other provenance-bearing Earth-observation inputs"
  "UAV multispectral/hyperspectral/thermal/LiDAR/photogrammetry only where lawful, proportionate and locally governed"
  "ground truth, grower observations and community/Indigenous knowledge remain independent evidence strands"
  "multi-season historical baseline rather than one-image diagnosis"
  "crop/site-specific calibration; model transferability is not assumed"
  "cloud, revisit, resolution, sensor, occlusion, domain-shift and calibration uncertainty"
  "Two-Eyed Seeing / pattern-mind strand preserved without epistemic fusion"
  "Mabo/Country/community authority and consent remain separate from technical observability"
  "precision agriculture recommendation is not intervention authority until required governance/consent axes are paid"
  false refl

record AgroecologySourcePacket : Set where
  constructor agroecology-source-packet
  field
    nasaReference : String
    faoReference : String
    orchardReviewReference : String
    uavSatelliteSynergyReference : String
    agroforestryReference : String
    boundedReading : String

agroecologySourcePacket : AgroecologySourcePacket
agroecologySourcePacket = agroecology-source-packet
  "NASA Landsat Agriculture & Food Security / OpenET: field-scale crop health, irrigation/water-use, drought and yield-support observations"
  "FAO Geospatial land-cover and crop monitoring: remote sensing for crop mapping, yield estimation, forecasting and statistically supported in-situ collection"
  "Crop Protection 195 (2025) 107240: UAV remote sensing across orchard pest/disease, irrigation, pruning, thinning and harvest management"
  "ISPRS JPRS 239 (2026) 908-927, DOI 10.1016/j.isprsjprs.2026.06.038: UAV-satellite synergies for multi-scale crop monitoring"
  "Remote Sensing Applications: Society and Environment 42 (2026) 101966: LiDAR + multispectral monitoring of heterogeneous agroforestry systems"
  "remote sensing can materially improve observation resolution, but a remotely sensed ecological state is not the whole situated LES planning state"

lesPlanningBoundaryReference : String
lesPlanningBoundaryReference =
  "LES full planning signature retains management history, ecological relation, knowledge provenance and justice coordinates; coarse remote sensing cannot recover erased axes"

twoEyedBoundaryReference : String
twoEyedBoundaryReference =
  "shared ecological observation does not fuse knowledge history; community authority/outcome remains independently capable of reopening implementation"

------------------------------------------------------------------------
-- 4. Cuba / Venezuela / international-law accountability packets.
------------------------------------------------------------------------

data InternationalAccountabilityCoordinate : Set where
  sanctionsAndEmbargo : InternationalAccountabilityCoordinate
  extraterritorialEconomicCoercion : InternationalAccountabilityCoordinate
  sovereignEquality : InternationalAccountabilityCoordinate
  nonIntervention : InternationalAccountabilityCoordinate
  prohibitionUseOfForce : InternationalAccountabilityCoordinate
  detentionOrRendition : InternationalAccountabilityCoordinate
  headOfStateImmunity : InternationalAccountabilityCoordinate
  humanRights : InternationalAccountabilityCoordinate
  resourceControl : InternationalAccountabilityCoordinate
  civilianHarm : InternationalAccountabilityCoordinate

record InternationalSourcePacket : Set where
  constructor international-source-packet
  field
    caseReference : String
    coordinates : List InternationalAccountabilityCoordinate
    primarySourceReference : String
    institutionalSpeakerReference : String
    boundedClaimReference : String
    contraryOrAdverseSourceReference : String
    legalConclusionRequiresSpecificAuthority : Bool
    legalConclusionRequiresSpecificAuthorityIsTrue : legalConclusionRequiresSpecificAuthority ≡ true

cubaUSPacket : InternationalSourcePacket
cubaUSPacket = international-source-packet
  "United States-Cuba sanctions/embargo relation"
  (sanctionsAndEmbargo ∷ extraterritorialEconomicCoercion ∷ sovereignEquality ∷ nonIntervention ∷ humanRights ∷ [])
  "UN General Assembly A/RES/80/4 (2025-10-29), Necessity of ending the economic, commercial and financial embargo imposed by the United States against Cuba; UN Secretary-General report A/80/83; US Treasury OFAC Cuba sanctions programme including E.O. 14404 and CACR"
  "UN General Assembly / Secretary-General and, separately, U.S. Treasury as primary institutional sources for their own acts/positions"
  "the UNGA again called for ending the embargo, while U.S. primary sources establish the continuing and expanded sanctions architecture; impacts/legality/remedy must be proposition- and authority-specific"
  "U.S. executive/legal rationale and Cuba/other-state submissions remain separately attributed rather than collapsed"
  true refl

maduroCapturePacket : InternationalSourcePacket
maduroCapturePacket = international-source-packet
  "United States military action in Venezuela and capture/detention of Nicolás Maduro, 2026-01-03"
  (sovereignEquality ∷ nonIntervention ∷ prohibitionUseOfForce ∷ detentionOrRendition ∷ headOfStateImmunity ∷ humanRights ∷ resourceControl ∷ civilianHarm ∷ [])
  "UN Secretary-General statement 2026-01-03 and Security Council remarks 2026-01-05; UN document A/80/586-S/2026/5; U.S. criminal proceedings and executive statements must remain separate primary fibres"
  "UN Secretary-General / Venezuela / United States each remain attributed to their own statements and legal positions"
  "the Secretary-General stated deep concern that international-law rules had not been respected and emphasized Charter Article 2(4); Maduro's criminal liability/immunity and operation legality remain separate legal questions"
  "U.S. asserted law-enforcement/security justifications and domestic indictments are adverse/contrary source fibres, not silently erased"
  true refl

------------------------------------------------------------------------
-- 5. Highest-alpha diagnosis route shared by market, LES and international
-- accountability: visible concern -> residual -> first missing prerequisite ->
-- least intrusive / highest information-value next observation.
------------------------------------------------------------------------

record HighestAlphaDiagnosisRoute : Set where
  constructor highest-alpha-diagnosis-route
  field
    diagnosedConcern : Diagnosis.DiagnosedWorldConcern
    firstMissingPrerequisiteReference : String
    candidateObservationReferences : List String
    expectedResidualReductionReference : String
    privacyBurdenReference : String
    nonDominationBurdenReference : String
    sourceDiligence : Diagnosis.SourceDiligence
    leastIntrusiveCandidateReference : String
    highestAlphaCandidateReference : String
    selectedCandidateReference : String
    selectionTradeoffReference : String
    selectionCreatesFact : Bool
    selectionCreatesFactIsFalse : selectionCreatesFact ≡ false

------------------------------------------------------------------------
-- 6. Canonical boundaries.
------------------------------------------------------------------------

record MarketAgroecologyInternationalBoundary : Set where
  constructor market-agroecology-international-boundary
  field
    marketAnomalyEqualsInsiderTrading : Bool
    marketAnomalyEqualsInsiderTradingIsFalse : marketAnomalyEqualsInsiderTrading ≡ false
    publicTradeDataCreatesTraderIdentity : Bool
    publicTradeDataCreatesTraderIdentityIsFalse : publicTradeDataCreatesTraderIdentity ≡ false
    activistFindingCreatesTradeAuthority : Bool
    activistFindingCreatesTradeAuthorityIsFalse : activistFindingCreatesTradeAuthority ≡ false
    profitableTradeCreatesEpistemicAuthority : Bool
    profitableTradeCreatesEpistemicAuthorityIsFalse : profitableTradeCreatesEpistemicAuthority ≡ false
    satelliteCropHealthEqualsWholeLESState : Bool
    satelliteCropHealthEqualsWholeLESStateIsFalse : satelliteCropHealthEqualsWholeLESState ≡ false
    remoteSensingCreatesLandInterventionAuthority : Bool
    remoteSensingCreatesLandInterventionAuthorityIsFalse : remoteSensingCreatesLandInterventionAuthority ≡ false
    technicalPrecisionErasesCountryAuthority : Bool
    technicalPrecisionErasesCountryAuthorityIsFalse : technicalPrecisionErasesCountryAuthority ≡ false
    ungaResolutionEqualsBindingCourtJudgment : Bool
    ungaResolutionEqualsBindingCourtJudgmentIsFalse : ungaResolutionEqualsBindingCourtJudgment ≡ false
    unSecretaryGeneralStatementEqualsIndividualCriminalJudgment : Bool
    unSecretaryGeneralStatementEqualsIndividualCriminalJudgmentIsFalse : unSecretaryGeneralStatementEqualsIndividualCriminalJudgment ≡ false
    sourceAttributionMustRemainActorSpecific : Bool
    sourceAttributionMustRemainActorSpecificIsTrue : sourceAttributionMustRemainActorSpecific ≡ true

canonicalMarketAgroecologyInternationalBoundary : MarketAgroecologyInternationalBoundary
canonicalMarketAgroecologyInternationalBoundary = market-agroecology-international-boundary
  false refl false refl false refl false refl false refl false refl false refl false refl false refl true refl
