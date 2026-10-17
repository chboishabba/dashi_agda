module DASHI.Physics.Thermodynamics.MagnothermAttributedEvidenceExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- MAGNOTHERM attributed evidence atlas.
--
-- Attribution discipline:
--   * source identity / authorship / access carrier / claim role are separate;
--   * primaryness is claim-relative;
--   * an archive or index does not become the paper's author or authority;
--   * peer-reviewed observation, vendor claim, planned future work and DASHI
--     reconstruction are different evidence roles;
--   * citation and acquisition do not import proof or calibrated-device status.
------------------------------------------------------------------------

stableOperationArticle : Source.AttributedSource
stableOperationArticle =
  Source.mkDOISource
    "Nico P. Weiß; Ulysse Rocabert; Cornelia Hoppe; Jens-Peter Zwick; Konrad Loewe; Maximilian Fries; Antti J. Karttunen; Oliver Gutfleisch; Falk Muench"
    "Stable Operation of Copper-Protected La(FeMnSi)13Hy Regenerators in a Magnetic Cooling Unit"
    "ACS Applied Engineering Materials 3(1):256-265"
    "2025"
    "10.1021/acsaenm.4c00747"
    "https://pubs.acs.org/doi/10.1021/acsaenm.4c00747"
    Source.academicArticleSource
    "primary peer-reviewed source for the paper's reported material identity, protection strategy, magnetocaloric characterization, in-device aging observations, bounded six-week result, preliminary three-month microchannel result, and stated future-work plan; not device-COP authority"
    Source.publicAttribution

magnothermTechnologyPage : Source.AttributedSource
magnothermTechnologyPage =
  Source.mkNoDOISource
    "MAGNOTHERM Solutions GmbH"
    "Technology"
    "MAGNOTHERM corporate technology page"
    "2026"
    "https://www.magnotherm.com/technology"
    Source.institutionalSource
    "primary source for MAGNOTHERM's own current technology descriptions and performance claims; vendor self-description, not independent calibration"
    Source.publicAttribution

magnothermStellarPage : Source.AttributedSource
magnothermStellarPage =
  Source.mkNoDOISource
    "MAGNOTHERM Solutions GmbH"
    "STELLAR - Magnetic Cooling, Superconducted"
    "MAGNOTHERM development platform page"
    "2026"
    "https://www.magnotherm.com/stellar"
    Source.institutionalSource
    "primary source for MAGNOTHERM's own STELLAR targets, visions and availability statements; development claim, not achieved-device calibration"
    Source.publicAttribution

magnothermAttributedSourceAtlas : Source.AttributedSourceAtlas
magnothermAttributedSourceAtlas =
  Source.mkSourceAtlas
    "MAGNOTHERM magnetocaloric attributed source atlas"
    "DASHI.Physics.Thermodynamics.MagnothermAttributedEvidenceExact"
    (stableOperationArticle ∷ magnothermTechnologyPage ∷ magnothermStellarPage ∷ [])
    "claim-relative attribution for the ACS paper and current MAGNOTHERM technology/STELLAR pages; access carriers and DASHI reconstruction remain non-authoritative transformations"

magnothermAttributedSourceReceipt : Receipt.GenericReceipt
magnothermAttributedSourceReceipt =
  Source.attributedSourceAtlasReceipt
    magnothermAttributedSourceAtlas
    "source metadata and claim-role regression checked by MagnothermAttributionValidation; no Agda compiler receipt asserted here"

magnothermAttributedSourceReceiptNonPromoting :
  Receipt.promotesClaim magnothermAttributedSourceReceipt ≡ false
magnothermAttributedSourceReceiptNonPromoting = refl

------------------------------------------------------------------------
-- Access carriers are provenance/transport, not authorship.
------------------------------------------------------------------------

data AccessCarrierRole : Set where
  publisherRecord repositoryRelay bibliographicIndex : AccessCarrierRole

record SourceAccessCarrier (source : Source.AttributedSource) : Set where
  constructor sourceAccessCarrier
  field
    locator : String
    role : AccessCarrierRole
    accessedDate : String
    sameWorkIdentityEstablished : Bool
    carrierCreatesScientificAuthority : Bool
    carrierCreatesScientificAuthorityIsFalse :
      carrierCreatesScientificAuthority ≡ false

acsPublisherCarrier : SourceAccessCarrier stableOperationArticle
acsPublisherCarrier =
  sourceAccessCarrier
    "https://pubs.acs.org/doi/10.1021/acsaenm.4c00747"
    publisherRecord
    "2026-10-15"
    true
    false refl

pmcRelayCarrier : SourceAccessCarrier stableOperationArticle
pmcRelayCarrier =
  sourceAccessCarrier
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC11773641/"
    repositoryRelay
    "2026-10-15"
    true
    false refl

aaltoRepositoryCarrier : SourceAccessCarrier stableOperationArticle
aaltoRepositoryCarrier =
  sourceAccessCarrier
    "https://aaltodoc.aalto.fi/items/074cd7e5-61d2-4526-b452-4a54270f54f5"
    repositoryRelay
    "2026-10-15"
    true
    false refl

------------------------------------------------------------------------
-- Claim-relative payment.
------------------------------------------------------------------------

data ClaimRole : Set where
  peerReviewedObservation : ClaimRole
  peerReviewedMethod : ClaimRole
  vendorTechnologyClaim : ClaimRole
  vendorDevelopmentVision : ClaimRole
  plannedFutureExperiment : ClaimRole
  dashiFormalReconstruction : ClaimRole

data SameObjectStatus : Set where
  sameSourceObject : SameObjectStatus
  sameDeviceNotEstablished : SameObjectStatus
  crossObjectOnly : SameObjectStatus

record ClaimPayment : Set where
  constructor claimPayment
  field
    claimLabel : String
    source : Source.AttributedSource
    exactLocator : String
    role : ClaimRole
    sameObjectStatus : SameObjectStatus
    primaryForClaim : Bool
    preliminary : Bool
    empiricalPayment : Bool
    calibratedDeviceEvidence : Bool
    claimCeiling : String

inDeviceCompositionPayment : ClaimPayment
inDeviceCompositionPayment =
  claimPayment
    "the in-device microchannel regenerators were purchased from VACUUMSCHMELZE and identified within an approximate Mn-substituted, fully hydrogenated La-Fe-Si composition envelope"
    stableOperationArticle
    "Materials and Methods: hydrogenated and Mn-substituted LaFeSi microchannel regenerators purchased for in-device testing; Introduction/Abbreviations give the approximate composition envelope"
    peerReviewedMethod
    sameSourceObject
    true false true false
    "same-study material identity and bounded composition envelope; not exact batch stoichiometry, phase fractions, magnetic symmetry, constitutive response or calibrated device performance"

sixWeekContinuedOperationPayment : ClaimPayment
sixWeekContinuedOperationPayment =
  claimPayment
    "protected regenerators remained almost indistinguishable from their prior state after six weeks of continued operation"
    stableOperationArticle
    "Results and Discussion: paragraph beginning 'After 6 weeks of continued operation'"
    peerReviewedObservation
    sameSourceObject
    true false true false
    "bounded six-week in-device aging observation for the studied protected regenerators; not product lifetime and not device COP"

threeMonthMicrochannelPayment : ClaimPayment
threeMonthMicrochannelPayment =
  claimPayment
    "preliminary ongoing result reports preservation of pristine microchannel state after three months"
    stableOperationArticle
    "Results and Discussion; Supporting Information Figure SI9"
    peerReviewedObservation
    sameSourceObject
    true true true false
    "preliminary three-month microchannel observation; does not establish multi-year service life, full performance retention, or commercial-device lifetime"

oneTeslaAdiabaticCharacterizationPayment : ClaimPayment
oneTeslaAdiabaticCharacterizationPayment =
  claimPayment
    "coated and pristine microchannel regenerators were characterized by adiabatic temperature change under a 1 T field and plating did not deteriorate the reported magnetocaloric function"
    stableOperationArticle
    "Figure 4(c); Assessment of Magnetocaloric Function"
    peerReviewedObservation
    sameSourceObject
    true false true false
    "bounded 1 T delta-T_ad characterization/function check for the studied regenerators; not a complete M(T,H), S(T,H), c_H(T,H) constitutive surface and not device COP"

agingTestOperatingPointPayment : ClaimPayment
agingTestOperatingPointPayment =
  claimPayment
    "modified POLARIS load-free in-device aging operated media near the Curie temperature (~288 K), at 2 Hz magnetisation and a reported ~0.8 T field"
    stableOperationArticle
    "In-Device Testing"
    peerReviewedMethod
    sameSourceObject
    true false true false
    "bounded same-study aging-test operating point; not a spatial/temporal B-H field map, complete field/flow phase timing, loaded cooling capacity, or COP calibration"

longTermExperimentPlanPayment : ClaimPayment
longTermExperimentPlanPayment =
  claimPayment
    "authors state an intention to pursue long-term experiments lasting several months to years"
    stableOperationArticle
    "Results and Discussion: paragraph following the preliminary three-month result"
    plannedFutureExperiment
    sameSourceObject
    true false false false
    "prospective experiment plan only; cannot be used as evidence that months-to-years performance has already been observed"

vendorThirtyPercentWorkRecoveryPayment : ClaimPayment
vendorThirtyPercentWorkRecoveryPayment =
  claimPayment
    "rotational balancing allows recovery of work, claimed to increase cycle efficiency by up to 30% against alternatives"
    magnothermTechnologyPage
    "Technology: 'How is this process more efficient?'"
    vendorTechnologyClaim
    sameDeviceNotEstablished
    true false false false
    "MAGNOTHERM vendor technology claim; requires same-device energy accounting and independent/calibrated validation before COP or efficiency promotion"

stellarFiveTeslaTargetPayment : ClaimPayment
stellarFiveTeslaTargetPayment =
  claimPayment
    "5 T is the target field for STELLAR"
    magnothermStellarPage
    "STELLAR: FAQ 'What logic is behind the 100x power gain from 1T to 5T?'"
    vendorDevelopmentVision
    sameDeviceNotEstablished
    true false false false
    "development target reported by MAGNOTHERM; not a measured production-device field map"

stellar125kWModuleVisionPayment : ClaimPayment
stellar125kWModuleVisionPayment =
  claimPayment
    "STELLAR vision states 125 kW+ modules"
    magnothermStellarPage
    "STELLAR: The Vision"
    vendorDevelopmentVision
    sameDeviceNotEstablished
    true false false false
    "vendor module vision; not measured cooling capacity of a same-object calibrated device"

stellar250kWDepictionPayment : ClaimPayment
stellar250kWDepictionPayment =
  claimPayment
    "STELLAR page depicts two modules as 250 kW+ within a 20 ft container footprint"
    magnothermStellarPage
    "STELLAR: The Vision, two-module depiction"
    vendorDevelopmentVision
    sameDeviceNotEstablished
    true false false false
    "vendor design depiction/vision; not independently observed 250 kW device performance"

currentClaimPayments : List ClaimPayment
currentClaimPayments =
  inDeviceCompositionPayment
  ∷ sixWeekContinuedOperationPayment
  ∷ threeMonthMicrochannelPayment
  ∷ oneTeslaAdiabaticCharacterizationPayment
  ∷ agingTestOperatingPointPayment
  ∷ longTermExperimentPlanPayment
  ∷ vendorThirtyPercentWorkRecoveryPayment
  ∷ stellarFiveTeslaTargetPayment
  ∷ stellar125kWModuleVisionPayment
  ∷ stellar250kWDepictionPayment
  ∷ []

------------------------------------------------------------------------
-- Attribution firewall / source ceiling.
------------------------------------------------------------------------

record MagnothermAttributionFirewall : Set where
  constructor magnotherm-attribution-firewall
  field
    sourceIdentitySeparateFromAuthority : Bool
    accessCarrierSeparateFromAuthorship : Bool
    primarynessIsClaimRelative : Bool
    peerReviewedObservationSeparateFromVendorClaim : Bool
    vendorClaimSeparateFromIndependentCalibration : Bool
    futurePlanSeparateFromCompletedExperiment : Bool
    sourceClaimSeparateFromDASHIReconstruction : Bool
    sameDevicePaymentRequiredForDevicePerformance : Bool
    citationDoesNotImportProof : Bool

canonicalMagnothermAttributionFirewall : MagnothermAttributionFirewall
canonicalMagnothermAttributionFirewall =
  magnotherm-attribution-firewall
    true true true true true true true true true
