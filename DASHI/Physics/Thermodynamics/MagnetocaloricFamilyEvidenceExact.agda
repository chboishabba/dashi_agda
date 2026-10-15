module DASHI.Physics.Thermodynamics.MagnetocaloricFamilyEvidenceExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- Cross-object La-Fe-(Mn)-Si-H family evidence.
--
-- These papers pay family-level physical structure/response facts.  They do
-- not identify the exact MAGNOTHERM regenerator, coating batch or device.
------------------------------------------------------------------------

radulov2017 : Source.AttributedSource
radulov2017 =
  Source.mkDOISource
    "I. A. Radulov; D. Yu. Karpenkov; K. P. Skokov; A. Yu. Karpenkov; T. Braun; V. Brabänder; T. Gottschall; M. Pabst; B. Stoll; O. Gutfleisch"
    "Production and properties of metal-bonded La(Fe,Mn,Si)13Hx composite material"
    "Acta Materialia 127:389-399"
    "2017"
    "10.1016/j.actamat.2017.01.054"
    "https://doi.org/10.1016/j.actamat.2017.01.054"
    Source.academicArticleSource
    "cross-object family evidence for NaZn13 crystal structure, near-room-temperature transition, direct delta-T_ad field characterization, magnetovolume fatigue and thermal/mechanical/chemical composite behavior"
    Source.publicAttribution

krautz2014 : Source.AttributedSource
krautz2014 =
  Source.mkDOISource
    "M. Krautz; K. P. Skokov; T. Gottschall; C. S. Teixeira; A. Waske; J. Liu; L. Schultz; O. Gutfleisch"
    "Systematic investigation of Mn substituted La(Fe,Si)13 alloys and their hydrides for room-temperature magnetocaloric application"
    "Journal of Alloys and Compounds 598:27-32"
    "2014"
    "10.1016/j.jallcom.2014.02.015"
    "https://doi.org/10.1016/j.jallcom.2014.02.015"
    Source.academicArticleSource
    "cross-object family evidence for Mn/Si/hydrogenation dependence of transition temperature, phase formation, long-time stability of fully hydrogenated compositions and estimated optimal field/delta-T_ad conditions"
    Source.publicAttribution

piazzi2016 : Source.AttributedSource
piazzi2016 =
  Source.mkDOISource
    "M. Piazzi; C. Bennati; C. Curcio; M. Kuepferling; V. Basso"
    "Modeling specific heat and entropy change in La(Fe-Mn-Si)13-H compounds"
    "Journal of Magnetism and Magnetic Materials 400:349-355"
    "2016"
    "10.1016/j.jmmm.2015.07.055"
    "https://doi.org/10.1016/j.jmmm.2015.07.055"
    Source.academicArticleSource
    "cross-object family evidence combining measured field-dependent specific heat with magnetoelastic modeling of entropy, first-order transition and Mn-dependent exchange coupling"
    Source.publicAttribution

fukamichi2006 : Source.AttributedSource
fukamichi2006 =
  Source.mkDOISource
    "K. Fukamichi; A. Fujita; S. Fujieda"
    "Large magnetocaloric effects and thermal transport properties of La(FeSi)13 and their hydrides"
    "Journal of Alloys and Compounds 408-412:307-312"
    "2006"
    "10.1016/j.jallcom.2005.04.022"
    "https://doi.org/10.1016/j.jallcom.2005.04.022"
    Source.academicArticleSource
    "cross-object family evidence for hydrogen-controlled Curie temperature, preserved itinerant-electron metamagnetic response, delta-S/delta-T_ad behavior and thermal conductivity"
    Source.publicAttribution

magnetocaloricFamilySourceAtlas : Source.AttributedSourceAtlas
magnetocaloricFamilySourceAtlas =
  Source.mkSourceAtlas
    "La-Fe-(Mn)-Si-H magnetocaloric family source atlas"
    "DASHI.Physics.Thermodynamics.MagnetocaloricFamilyEvidenceExact"
    (radulov2017 ∷ krautz2014 ∷ piazzi2016 ∷ fukamichi2006 ∷ [])
    "family-level physical evidence used only through explicit cross-object claim payments; exact MAGNOTHERM material/device identity remains a separate obligation"

------------------------------------------------------------------------
-- Claim payments.
------------------------------------------------------------------------

data FamilyObjectStatus : Set where
  crossObjectFamilyEvidence : FamilyObjectStatus
  sameMaterialObjectEstablished : FamilyObjectStatus

data FamilyClaimRole : Set where
  crystallographicObservation : FamilyClaimRole
  compositionHydrogenationObservation : FamilyClaimRole
  thermodynamicMeasurement : FamilyClaimRole
  modelConstrainedInterpretation : FamilyClaimRole
  thermalTransportObservation : FamilyClaimRole

record FamilyClaimPayment : Set where
  constructor familyClaimPayment
  field
    claimLabel : String
    source : Source.AttributedSource
    exactLocator : String
    role : FamilyClaimRole
    sameObjectStatus : FamilyObjectStatus
    empiricalPayment : Bool
    modelMediated : Bool
    claimCeiling : String

radulovCrystalStructurePayment : FamilyClaimPayment
radulovCrystalStructurePayment =
  familyClaimPayment
    "LaFe11.38Mn0.32Si1.30Hx precursor has a main cubic NaZn13 phase with a = 11.568 +/- 0.002 Å, transition near 297 K, and secondary phases reported by XRD/SEM"
    radulov2017
    "Sample characterization; Magnetocaloric La(Fe,Mn,Si)13Hx material"
    crystallographicObservation
    crossObjectFamilyEvidence
    true false
    "direct evidence for that commercial precursor composition; establishes a strong family-level crystal/transition witness but not the exact MAGNOTHERM sample identity or magnetic space group"

radulovMagnetovolumeTransportPayment : FamilyClaimPayment
radulovMagnetovolumeTransportPayment =
  familyClaimPayment
    "La(Fe,Mn,Si)13Hx composites exhibit large magnetovolume-driven cyclic mechanical stress; the study measures direct delta-T_ad(H) up to 1.93 T and investigates heat-flow/thermal, mechanical and chemical properties"
    radulov2017
    "Abstract; Introduction; Sample characterization; Heat flow dynamics"
    thermalTransportObservation
    crossObjectFamilyEvidence
    true false
    "family-level evidence for coupled magnetocaloric/thermal/mechanical design; not same-device heat-transfer coefficient, fatigue lifetime or hydraulic closure"

krautzHydrogenationTuningPayment : FamilyClaimPayment
krautzHydrogenationTuningPayment =
  familyClaimPayment
    "Mn substitution and Si content tune transition behavior, while hydrogen uptake shifts the room-temperature operating point and fully hydrogenated compositions avoid previously reported phase coexistence instability"
    krautz2014
    "Highlights; Abstract; composition series before/after hydrogenation"
    compositionHydrogenationObservation
    crossObjectFamilyEvidence
    true false
    "empirical family-level composition/hydrogenation map; not a calibrated response surface for the exact MAGNOTHERM alloy batch"

piazziMagnetoelasticSpecificHeatPayment : FamilyClaimPayment
piazziMagnetoelasticSpecificHeatPayment =
  familyClaimPayment
    "field-dependent specific heat and entropy behavior of LaFexMnySiz-H1.65 is interpreted with a magnetoelastic Bean-Rodbell model; Mn-dependent exchange and volume-exchange coupling control the first-order transition"
    piazzi2016
    "Abstract; measured specific heat in field; magnetoelastic model"
    modelConstrainedInterpretation
    crossObjectFamilyEvidence
    true true
    "measured thermodynamic data plus model-constrained interpretation; model agreement does not identify a microscopic Hamiltonian or exact-device free-energy surface"

fukamichiHydrideTransportPayment : FamilyClaimPayment
fukamichiHydrideTransportPayment =
  familyClaimPayment
    "hydrogen concentration shifts La(Fe,Si)13-family Curie temperature from cryogenic toward room-temperature operation while preserving large MCE, with thermal conductivity investigated alongside delta-S and delta-T_ad"
    fukamichi2006
    "Abstract; experiments; conclusion"
    thermalTransportObservation
    crossObjectFamilyEvidence
    true false
    "family-level hydrogen/MCE/thermal-transport evidence; not same-material Mn-containing calibration and not device heat-transfer closure"

familyClaimPayments : List FamilyClaimPayment
familyClaimPayments =
  radulovCrystalStructurePayment
  ∷ radulovMagnetovolumeTransportPayment
  ∷ krautzHydrogenationTuningPayment
  ∷ piazziMagnetoelasticSpecificHeatPayment
  ∷ fukamichiHydrideTransportPayment
  ∷ []

record FamilyEvidenceFirewall : Set where
  constructor family-evidence-firewall
  field
    familyEvidenceIsNotSameMaterialIdentity : Bool
    familyEvidenceIsNotSameDeviceEvidence : Bool
    modelAgreementIsNotMicroscopicHamiltonianValidation : Bool
    crystalTypeIsNotMagneticSpaceGroup : Bool
    thermalConductivityIsNotHeatTransferCoefficient : Bool
    deltaTadCurveIsNotFullConstitutiveSurface : Bool
    sameMaterialIdentityStillRequired : Bool
    sameDeviceCalibrationStillRequired : Bool

canonicalFamilyEvidenceFirewall : FamilyEvidenceFirewall
canonicalFamilyEvidenceFirewall =
  family-evidence-firewall true true true true true true true true
