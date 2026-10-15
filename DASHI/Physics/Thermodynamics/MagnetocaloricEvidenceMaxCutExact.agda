module DASHI.Physics.Thermodynamics.MagnetocaloricEvidenceMaxCutExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Thermodynamics.MagnothermAttributedEvidenceExact as Evidence

------------------------------------------------------------------------
-- Terminal evidence-payment atlas for the current magnetocaloric max-cut.
--
-- This module does not turn a source into a theorem.  It records which
-- obligations have actually been paid, by what source role, and which hard
-- frontier still requires same-object empirical acquisition/calibration.
------------------------------------------------------------------------

data PaymentStatus : Set where
  peerReviewedPaid : PaymentStatus
  peerReviewedPartial : PaymentStatus
  vendorSourceOnly : PaymentStatus
  structurallyTyped : PaymentStatus
  structuralPrecedentOnly : PaymentStatus
  openSameObjectAcquisition : PaymentStatus

data PaymentQualifier : Set where
  directObservation : PaymentQualifier
  preliminaryOnly : PaymentQualifier
  boundedAgingOnly : PaymentQualifier
  vendorClaimOnly : PaymentQualifier
  plannedOnly : PaymentQualifier
  typedButUncalibrated : PaymentQualifier
  reusableMathematicsOnly : PaymentQualifier
  noSameObjectData : PaymentQualifier

record PaymentRow : Set where
  constructor paymentRow
  field
    obligation : String
    sourceOwner : String
    status : PaymentStatus
    qualifier : PaymentQualifier
    sameObjectRequired : Bool
    authorityBoundary : String
    nextPayment : String

sixWeekAgingRow : PaymentRow
sixWeekAgingRow =
  paymentRow
    "protected LaFeSi regenerator aging under continued in-device operation"
    "Weiß et al. 2025, DOI 10.1021/acsaenm.4c00747"
    peerReviewedPaid
    boundedAgingOnly
    true
    "paper supports the studied protected regenerators for the reported six-week window; it does not establish product lifetime"
    "extend with same-object longer-duration chemical/mechanical/functional time series"

threeMonthMicrochannelRow : PaymentRow
threeMonthMicrochannelRow =
  paymentRow
    "microchannel preservation after three months"
    "Weiß et al. 2025, Supporting Information Figure SI9"
    peerReviewedPaid
    preliminaryOnly
    true
    "reported as a preliminary ongoing result; channel appearance is not full lifetime or COP"
    "acquire completed long-duration same-object performance and degradation series"

longTermLifetimeRow : PaymentRow
longTermLifetimeRow =
  paymentRow
    "months-to-years service-life evidence"
    "Weiß et al. 2025 future-work statement"
    openSameObjectAcquisition
    plannedOnly
    true
    "the paper explicitly describes months-to-years experiments as future work"
    "completed longitudinal same-object aging/performance data approaching product-life timescales"

protectionChemistryRow : PaymentRow
protectionChemistryRow =
  paymentRow
    "Cu coating + inhibitor protection mechanism under application-relevant operation"
    "Weiß et al. 2025"
    peerReviewedPartial
    directObservation
    true
    "paper supports the reported protection strategy and bounded aging observations; full lifetime transfer across fluids/coating thicknesses remains open"
    "material-specific corrosion kinetics, coating/interface fatigue and fluid-specific qualification over the intended lifetime"

vendorThirtyPercentRow : PaymentRow
vendorThirtyPercentRow =
  paymentRow
    "up-to-30% cycle-efficiency increase from rotational work recovery"
    "MAGNOTHERM Technology page"
    vendorSourceOnly
    vendorClaimOnly
    true
    "primary for what MAGNOTHERM currently claims, not independent device calibration"
    "same-device cooling energy, gross input work, recovered work and uncertainty accounting"

stellarFiveTeslaRow : PaymentRow
stellarFiveTeslaRow =
  paymentRow
    "5 T STELLAR target field"
    "MAGNOTHERM STELLAR page"
    vendorSourceOnly
    vendorClaimOnly
    true
    "development target, not an independently measured production-device field map"
    "same-object spatial/temporal B-H field map and magnet operating envelope"

stellarCapacityRow : PaymentRow
stellarCapacityRow =
  paymentRow
    "125 kW+ modules and depicted 250 kW+ two-module STELLAR configuration"
    "MAGNOTHERM STELLAR page"
    vendorSourceOnly
    vendorClaimOnly
    true
    "vendor vision/design depiction; no promotion to achieved capacity"
    "same-device calorimetric capacity measurement over declared operating conditions"

materialConstitutiveRow : PaymentRow
materialConstitutiveRow =
  paymentRow
    "material-specific M(T,H), S(T,H), c_H(T,H), delta-S and delta-T_ad surfaces"
    "magnetocaloric material consumer interface"
    structurallyTyped
    typedButUncalibrated
    true
    "generic response laws are typed; a concrete LaFeSi constitutive surface is not supplied by structure alone"
    "acquire calibrated material tables/curves with composition, temperature, field convention and uncertainty"

crystalMagneticIdentificationRow : PaymentRow
crystalMagneticIdentificationRow =
  paymentRow
    "same-material crystal phase and magnetic symmetry identification"
    "condensed-matter consumer interface"
    structurallyTyped
    typedButUncalibrated
    true
    "group-action and observable-fibre machinery is reusable, but does not identify the actual material phase"
    "source-backed crystallography/magnetic-order object welded to the studied composition and operating regime"

quantumFreeEnergyRow : PaymentRow
quantumFreeEnergyRow =
  paymentRow
    "validated Hamiltonian -> ensemble -> free-energy -> M/S/C chain"
    "quantum/statistical consumer interface"
    structurallyTyped
    typedButUncalibrated
    true
    "finite or model Hamiltonian does not establish bulk thermodynamics"
    "validated electronic model plus ensemble/thermodynamic-limit and material-response calibration"

fieldMapRow : PaymentRow
fieldMapRow =
  paymentRow
    "same-device electromagnetic B/H field map"
    "U(1) electromagnetic consumer interface"
    structurallyTyped
    typedButUncalibrated
    true
    "tesla-valued B and A/m-valued H are typed separately; constitutive relation and geometry remain empirical"
    "measured or validated simulated field map with B-H convention, geometry and operating-current/magnet state"

hydraulicsRow : PaymentRow
hydraulicsRow =
  paymentRow
    "porous-regenerator pressure drop and flow calibration"
    "continuum/regenerator consumer interface"
    structurallyTyped
    noSameObjectData
    true
    "mass/momentum/energy balances are relevant but do not manufacture hydraulic coefficients"
    "same-regenerator delta-p versus flow data and calibrated porous closure"

heatTransferRow : PaymentRow
heatTransferRow =
  paymentRow
    "solid-fluid heat-transfer calibration"
    "continuum/regenerator consumer interface"
    structurallyTyped
    noSameObjectData
    true
    "Fourier/energy-balance structure is present; transfer coefficients and contact resistances remain physical inputs"
    "same-regenerator thermal response/transfer calibration across the operating envelope"

cycleTimingRow : PaymentRow
cycleTimingRow =
  paymentRow
    "field/flow cycle timing and controller calibration"
    "ActiveMagneticRegenerator synchronisation interface"
    structurallyTyped
    noSameObjectData
    true
    "four-phase synchronisation is explicit but not numerically calibrated"
    "same-device timing traces, valve/pump/magnet phase relation and control-error envelope"

sameDeviceCOPRow : PaymentRow
sameDeviceCOPRow =
  paymentRow
    "same-device COP validation"
    "ProtectedMagnetocaloricSystem energy accounting"
    openSameObjectAcquisition
    noSameObjectData
    true
    "vendor or component claims cannot replace same-object first-law work/cooling accounting"
    "simultaneous same-device cooling energy, field/motor/pump input, recovered work, parasitics and uncertainty"

sameDeviceCapacityRow : PaymentRow
sameDeviceCapacityRow =
  paymentRow
    "same-device cooling-capacity validation"
    "ProtectedMagnetocaloricSystem + regenerator thermal accounting"
    openSameObjectAcquisition
    noSameObjectData
    true
    "platform vision and material response do not establish delivered cooling capacity"
    "same-device calorimetric capacity over declared hot/cold temperatures, span, flow and field cycle"

navierStokesRow : PaymentRow
navierStokesRow =
  paymentRow
    "Navier-Stokes contribution to MAGNOTHERM lane"
    "DASHI continuum/NS machinery"
    structuralPrecedentOnly
    reusableMathematicsOnly
    false
    "generic balance/reduction machinery may be reused; Clay regularity is not AMR empirical payment"
    "none unless a concrete fluid reduction needs a reusable mathematical lemma"

yangMillsRow : PaymentRow
yangMillsRow =
  paymentRow
    "Yang-Mills contribution to MAGNOTHERM lane"
    "DASHI YM-derived generic operator/symmetry machinery"
    structuralPrecedentOnly
    reusableMathematicsOnly
    false
    "non-abelian Clay YM is not application magnetism; only already-factored generic mathematics is reusable"
    "none unless a domain-neutral theorem is consumed through an explicit adapter"

allPaymentRows : List PaymentRow
allPaymentRows =
  sixWeekAgingRow
  ∷ threeMonthMicrochannelRow
  ∷ longTermLifetimeRow
  ∷ protectionChemistryRow
  ∷ vendorThirtyPercentRow
  ∷ stellarFiveTeslaRow
  ∷ stellarCapacityRow
  ∷ materialConstitutiveRow
  ∷ crystalMagneticIdentificationRow
  ∷ quantumFreeEnergyRow
  ∷ fieldMapRow
  ∷ hydraulicsRow
  ∷ heatTransferRow
  ∷ cycleTimingRow
  ∷ sameDeviceCOPRow
  ∷ sameDeviceCapacityRow
  ∷ navierStokesRow
  ∷ yangMillsRow
  ∷ []

record MagnetocaloricMaxCutReceipt : Set where
  constructor magnetocaloric-max-cut-receipt
  field
    canonicalAttributionFirewallPresent : Bool
    peerReviewedAgingWindowPaid : Bool
    preliminaryThreeMonthProperlyQualified : Bool
    vendorClaimsRemainVendorClaims : Bool
    structuralConsumersPopulated : Bool
    nsAndYMRemainStructuralOnly : Bool
    noFabricatedSameDeviceCalibration : Bool
    hardFrontierIsEmpiricalAcquisition : Bool

canonicalMagnetocaloricMaxCutReceipt : MagnetocaloricMaxCutReceipt
canonicalMagnetocaloricMaxCutReceipt =
  magnetocaloric-max-cut-receipt
    true true true true true true true true
