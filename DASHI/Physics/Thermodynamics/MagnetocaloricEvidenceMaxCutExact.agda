module DASHI.Physics.Thermodynamics.MagnetocaloricEvidenceMaxCutExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Thermodynamics.MagnothermAttributedEvidenceExact as Evidence
import DASHI.Physics.Thermodynamics.MagnetocaloricFamilyEvidenceExact as Family
import DASHI.Physics.Thermodynamics.MagnothermPolarisEvidenceExact as Polaris

------------------------------------------------------------------------
-- Terminal evidence-payment atlas for the current magnetocaloric max-cut.
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

sameStudyCompositionRow : PaymentRow
sameStudyCompositionRow =
  paymentRow
    "same-study in-device regenerator material identity and bounded composition envelope"
    "Weiß et al. 2025, Materials and Methods / Introduction / Abbreviations"
    peerReviewedPaid directObservation true
    "the microchannel regenerators used for in-device testing are identified as VACUUMSCHMELZE Mn-substituted, fully hydrogenated LaFeSi within an approximate composition range; exact batch stoichiometry, phase fractions, magnetic symmetry and response surfaces are not supplied"
    "obtain exact batch chemistry/phase analysis and weld it to the measured response and in-device receipt"

sixWeekAgingRow : PaymentRow
sixWeekAgingRow =
  paymentRow
    "protected LaFeSi regenerator aging under continued in-device operation"
    "Weiß et al. 2025, DOI 10.1021/acsaenm.4c00747"
    peerReviewedPaid boundedAgingOnly true
    "paper supports the studied protected regenerators for the reported six-week window; it does not establish product lifetime"
    "extend with same-object longer-duration chemical/mechanical/functional time series"

threeMonthMicrochannelRow : PaymentRow
threeMonthMicrochannelRow =
  paymentRow
    "microchannel preservation after three months"
    "Weiß et al. 2025, Supporting Information Figure SI9"
    peerReviewedPaid preliminaryOnly true
    "reported as a preliminary ongoing result; channel appearance is not full lifetime or COP"
    "acquire completed long-duration same-object performance and degradation series"

oneTeslaAdiabaticCharacterizationRow : PaymentRow
oneTeslaAdiabaticCharacterizationRow =
  paymentRow
    "coated versus pristine microchannel regenerator magnetocaloric function under 1 T characterization"
    "Weiß et al. 2025, Figure 4(c) and Assessment of Magnetocaloric Function"
    peerReviewedPaid directObservation true
    "the paper reports adiabatic temperature-change characterization at 1 T and states that magnetocaloric function did not deteriorate during plating; this is not a full constitutive M/S/c_H surface"
    "digitized/calibrated delta-T_ad(T,B) and entropy/heat-capacity surfaces with composition, uncertainty and B/H convention"

agingTestOperatingPointRow : PaymentRow
agingTestOperatingPointRow =
  paymentRow
    "in-device aging-test operating point on modified POLARIS hardware"
    "Weiß et al. 2025, In-Device Testing"
    peerReviewedPartial directObservation true
    "load-free aging used media near Curie temperature (~288 K), 2 Hz magnetisation and a reported ~0.8 T field; this pays a bounded test condition, not a spatial/temporal field map, full AMR phase timing, loaded capacity or COP"
    "same-device synchronized field/flow traces, field map, loaded thermal duty and controller-error envelope"

------------------------------------------------------------------------
-- Cross-object La-Fe-(Mn)-Si-H family evidence.
------------------------------------------------------------------------

familyCrystalStructureRow : PaymentRow
familyCrystalStructureRow =
  paymentRow
    "La-Fe-Mn-Si-H family crystal/transition prior"
    "Radulov et al. 2017, DOI 10.1016/j.actamat.2017.01.054"
    peerReviewedPartial directObservation true
    "LaFe11.38Mn0.32Si1.30Hx is reported with a main cubic NaZn13 phase, a = 11.568 +/- 0.002 Å, transition near 297 K and secondary phases; this is cross-object family evidence, not identity of the MAGNOTHERM alloy or its magnetic space group"
    "weld source-backed crystallography and magnetic-order identification to the exact studied MAGNOTHERM composition/batch"

familyHydrogenationCompositionRow : PaymentRow
familyHydrogenationCompositionRow =
  paymentRow
    "Mn/Si/hydrogenation dependence of La-Fe-Mn-Si-H transition and magnetocaloric response"
    "Krautz et al. 2014, DOI 10.1016/j.jallcom.2014.02.015"
    peerReviewedPartial directObservation true
    "systematic before/after-hydrogenation composition series pays a family-level response prior and stability distinction for fully hydrogenated material; it does not calibrate the exact MAGNOTHERM batch"
    "identify exact Mn/Si/H content and acquire same-material transition/MCE response with uncertainty"

familySpecificHeatEntropyRow : PaymentRow
familySpecificHeatEntropyRow =
  paymentRow
    "field-dependent specific heat / entropy and magnetoelastic first-order-transition prior"
    "Piazzi et al. 2016, DOI 10.1016/j.jmmm.2015.07.055"
    peerReviewedPartial typedButUncalibrated true
    "measured specific heat is combined with a Bean-Rodbell magnetoelastic model; useful for the thermodynamic/mechanical bridge but model agreement does not validate a microscopic Hamiltonian or exact-material free-energy surface"
    "acquire exact-material c_H(T,H), entropy and strain/volume response; validate any microscopic-to-free-energy model separately"

familyThermalTransportRow : PaymentRow
familyThermalTransportRow =
  paymentRow
    "La-Fe-Si-H family hydrogen tuning and thermal-conductivity prior"
    "Fukamichi, Fujita & Fujieda 2006, DOI 10.1016/j.jallcom.2005.04.022; Radulov et al. 2017"
    peerReviewedPartial directObservation true
    "family literature measures thermal transport and shows hydrogen-controlled transition/MCE behavior; material thermal conductivity is not a same-device solid-fluid heat-transfer coefficient or contact-resistance closure"
    "acquire exact-regenerator thermal conductivity/contact/interface and same-device heat-transfer calibration"

------------------------------------------------------------------------
-- Same-platform POLARIS evidence with different optimized working material.
------------------------------------------------------------------------

polarisSystemPerformanceRow : PaymentRow
polarisSystemPerformanceRow =
  paymentRow
    "peer-reviewed POLARIS plug-in performance campaign"
    "Liang et al. 2026, DOI 10.1016/j.applthermaleng.2025.129144"
    peerReviewedPaid directObservation false
    "the optimized reported POLARIS configuration pays real system-level cooling/COP performance for Gd/GdEr: 131 W/kg specific cooling capacity, plug-in COP 1.0 and 5.4% second-law efficiency at 15 K, plus a 28.5 K maximum span; it does not pay LaFeSi same-material COP or STELLAR performance"
    "for LaFeSi closure, acquire same-material loaded-device cooling/work accounting on the LaFeSi regenerator stack"

polarisHydraulicCampaignRow : PaymentRow
polarisHydraulicCampaignRow =
  paymentRow
    "peer-reviewed POLARIS hydraulic/system optimization campaign"
    "Liang et al. 2026, measurement campaign and hydraulic test stand"
    peerReviewedPaid directObservation false
    "POLARIS has measured energetic/hydraulic/acoustic/material characterization and utilization-factor optimization; working-material/device configuration differs from the LaFeSi aging object"
    "weld equivalent pressure/flow/utilization traces to the exact LaFeSi regenerator and its pore geometry"

polarisCommercialDeploymentRow : PaymentRow
polarisCommercialDeploymentRow =
  paymentRow
    "POLARIS commercial deployment / TRL evidence"
    "Liang et al. 2026"
    peerReviewedPaid directObservation false
    "43 units and months-long supermarket deployment with stable 6 C cooling are reported for POLARIS; this is platform commercialization evidence, not LaFeSi coating lifetime or STELLAR validation"
    "retain deployment as platform evidence while independently qualifying each working-material/device stack"

longTermLifetimeRow : PaymentRow
longTermLifetimeRow =
  paymentRow
    "months-to-years service-life evidence for the LaFeSi protection stack"
    "Weiß et al. 2025 future-work statement"
    openSameObjectAcquisition plannedOnly true
    "the LaFeSi paper explicitly describes months-to-years experiments as future work; POLARIS commercial deployment with another working material does not close this"
    "completed longitudinal same-LaFeSi-object aging/performance data approaching product-life timescales"

protectionChemistryRow : PaymentRow
protectionChemistryRow =
  paymentRow
    "Cu coating + inhibitor protection mechanism under application-relevant operation"
    "Weiß et al. 2025"
    peerReviewedPartial directObservation true
    "paper supports the reported protection strategy and bounded aging observations; full lifetime transfer across fluids/coating thicknesses remains open"
    "material-specific corrosion kinetics, coating/interface fatigue and fluid-specific qualification over the intended lifetime"

vendorThirtyPercentRow : PaymentRow
vendorThirtyPercentRow =
  paymentRow
    "up-to-30% cycle-efficiency increase from rotational work recovery"
    "MAGNOTHERM Technology page"
    vendorSourceOnly vendorClaimOnly true
    "primary for what MAGNOTHERM currently claims, not independent device calibration; the POLARIS paper pays measured plug-in COP but does not by itself isolate the claimed 30% recovery contribution"
    "same-device recovered-work decomposition and uncertainty accounting for the claimed mechanism"

stellarFiveTeslaRow : PaymentRow
stellarFiveTeslaRow =
  paymentRow
    "5 T STELLAR target field"
    "MAGNOTHERM STELLAR page"
    vendorSourceOnly vendorClaimOnly true
    "development target, not an independently measured production-device field map"
    "same-object spatial/temporal B-H field map and magnet operating envelope"

stellarCapacityRow : PaymentRow
stellarCapacityRow =
  paymentRow
    "125 kW+ modules and depicted 250 kW+ two-module STELLAR configuration"
    "MAGNOTHERM STELLAR page"
    vendorSourceOnly vendorClaimOnly true
    "vendor vision/design depiction; POLARIS device measurements do not promote to STELLAR achieved capacity"
    "same-device STELLAR calorimetric capacity measurement over declared operating conditions"

materialConstitutiveRow : PaymentRow
materialConstitutiveRow =
  paymentRow
    "material-specific M(T,H), S(T,H), c_H(T,H), delta-S and delta-T_ad surfaces"
    "magnetocaloric material consumer + same-study/family evidence"
    structurallyTyped typedButUncalibrated true
    "same-study composition identity and a 1 T delta-T_ad function check plus family-level response literature are paid, but a calibrated constitutive surface for the exact batch is not"
    "acquire exact-batch material tables/curves with temperature, B/H convention, cycling history and uncertainty"

crystalMagneticIdentificationRow : PaymentRow
crystalMagneticIdentificationRow =
  paymentRow
    "same-material crystal phase and magnetic symmetry identification"
    "condensed-matter consumer + same-study composition + Radulov family crystal evidence"
    structurallyTyped typedButUncalibrated true
    "the in-device composition envelope is known and NaZn13 family structure is empirically paid cross-object, but exact batch phase fractions/crystallography and magnetic symmetry/order remain unidentified"
    "source-backed exact-batch crystallography and magnetic-order object welded to the in-device material identity"

quantumFreeEnergyRow : PaymentRow
quantumFreeEnergyRow =
  paymentRow
    "validated Hamiltonian -> ensemble -> free-energy -> M/S/C chain"
    "quantum/statistical consumer + Piazzi magnetoelastic thermodynamic model"
    structurallyTyped typedButUncalibrated true
    "family magnetoelastic modeling constrains a phenomenological free-energy route but does not validate a microscopic Hamiltonian or bulk quantum derivation"
    "validated electronic model plus ensemble/thermodynamic-limit and exact-material response calibration"

fieldMapRow : PaymentRow
fieldMapRow =
  paymentRow
    "same-LaFeSi-device electromagnetic B/H field map"
    "U(1) electromagnetic consumer interface"
    structurallyTyped typedButUncalibrated true
    "the LaFeSi aging experiment reports ~0.8 T; the newer POLARIS paper reports a system field for another material configuration, but neither supplies the required exact LaFeSi spatial/temporal B-H map"
    "measured or validated simulated LaFeSi-device field map with B-H convention, geometry and operating state"

hydraulicsRow : PaymentRow
hydraulicsRow =
  paymentRow
    "same-LaFeSi-regenerator pressure drop and flow calibration"
    "continuum/regenerator consumer interface"
    structurallyTyped typedButUncalibrated true
    "POLARIS system hydraulics are peer-reviewed and measured, but the acquired source does not identify them as closure for the exact LaFeSi corrosion-study regenerator"
    "same-LaFeSi-regenerator delta-p versus flow data and calibrated porous closure"

heatTransferRow : PaymentRow
heatTransferRow =
  paymentRow
    "same-LaFeSi solid-fluid heat-transfer calibration"
    "continuum/regenerator consumer + family thermal-transport evidence"
    structurallyTyped typedButUncalibrated true
    "material/composite thermal conductivity and heat-flow studies plus POLARIS system optimization pay strong priors, but not exact LaFeSi same-device h/contact/interfacial-area closure"
    "same-LaFeSi-regenerator dynamic thermal response/transfer calibration across the operating envelope"

cycleTimingRow : PaymentRow
cycleTimingRow =
  paymentRow
    "same-LaFeSi field/flow cycle timing and controller calibration"
    "ActiveMagneticRegenerator synchronisation interface"
    structurallyTyped typedButUncalibrated true
    "the aging test pays 2 Hz magnetisation and POLARIS validates optimization of a related platform, but exact LaFeSi field/flow phase relation and controller-error envelope remain unwelded"
    "same-LaFeSi-device timing traces, valve/pump/magnet phase relation and control-error envelope"

sameDeviceCOPRow : PaymentRow
sameDeviceCOPRow =
  paymentRow
    "same-LaFeSi-device COP validation"
    "ProtectedMagnetocaloricSystem energy accounting"
    openSameObjectAcquisition noSameObjectData true
    "POLARIS plug-in COP is peer-reviewed for an optimized Gd/GdEr configuration; it cannot substitute for loaded same-LaFeSi-object first-law work/cooling accounting, while the LaFeSi aging test was load-free"
    "simultaneous same-LaFeSi-device cooling energy, field/motor/pump input, recovered work, parasitics and uncertainty"

sameDeviceCapacityRow : PaymentRow
sameDeviceCapacityRow =
  paymentRow
    "same-LaFeSi-device cooling-capacity validation"
    "ProtectedMagnetocaloricSystem + regenerator thermal accounting"
    openSameObjectAcquisition noSameObjectData true
    "POLARIS has measured cooling capacity for another working-material configuration, while the acquired LaFeSi aging experiment is load-free"
    "same-LaFeSi-device calorimetric capacity over declared hot/cold temperatures, span, flow and field cycle"

navierStokesRow : PaymentRow
navierStokesRow =
  paymentRow
    "Navier-Stokes contribution to MAGNOTHERM lane"
    "DASHI continuum/NS machinery"
    structuralPrecedentOnly reusableMathematicsOnly false
    "generic balance/reduction machinery may be reused; Clay regularity is not AMR empirical payment"
    "none unless a concrete fluid reduction needs a reusable mathematical lemma"

yangMillsRow : PaymentRow
yangMillsRow =
  paymentRow
    "Yang-Mills contribution to MAGNOTHERM lane"
    "DASHI YM-derived generic operator/symmetry machinery"
    structuralPrecedentOnly reusableMathematicsOnly false
    "non-abelian Clay YM is not application magnetism; only already-factored generic mathematics is reusable"
    "none unless a domain-neutral theorem is consumed through an explicit adapter"

allPaymentRows : List PaymentRow
allPaymentRows =
  sameStudyCompositionRow
  ∷ sixWeekAgingRow
  ∷ threeMonthMicrochannelRow
  ∷ oneTeslaAdiabaticCharacterizationRow
  ∷ agingTestOperatingPointRow
  ∷ familyCrystalStructureRow
  ∷ familyHydrogenationCompositionRow
  ∷ familySpecificHeatEntropyRow
  ∷ familyThermalTransportRow
  ∷ polarisSystemPerformanceRow
  ∷ polarisHydraulicCampaignRow
  ∷ polarisCommercialDeploymentRow
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
    sameStudyCompositionIdentityPaid : Bool
    peerReviewedAgingWindowPaid : Bool
    preliminaryThreeMonthProperlyQualified : Bool
    oneTeslaMaterialFunctionCheckPaid : Bool
    agingOperatingPointPartiallyPaid : Bool
    familyCrystalThermoTransportEvidenceAcquired : Bool
    familyEvidenceKeptCrossObject : Bool
    polarisSystemPerformanceEvidenceAcquired : Bool
    polarisHydraulicEvidenceAcquired : Bool
    polarisEvidenceKeptSeparateFromLaFeSi : Bool
    vendorClaimsRemainVendorClaims : Bool
    structuralConsumersPopulated : Bool
    nsAndYMRemainStructuralOnly : Bool
    noFabricatedSameDeviceCalibration : Bool
    hardFrontierIsExactMaterialSameDeviceAcquisition : Bool

canonicalMagnetocaloricMaxCutReceipt : MagnetocaloricMaxCutReceipt
canonicalMagnetocaloricMaxCutReceipt =
  magnetocaloric-max-cut-receipt
    true true true true true true true true true true true true true true true true
