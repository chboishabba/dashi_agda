module DASHI.Applications.CounterUASOperationalSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- PRODUCT / REGULATORY SOURCE ATLAS
--
-- Kept separate from the academic SOTA atlas so vendor claims, independent
-- academic evidence, and Australian legal authority cannot collapse into one
-- provenance class.
------------------------------------------------------------------------

droneShieldRfAI3Launch2026 : Source.AttributedSource
droneShieldRfAI3Launch2026 =
  Source.mkNoDOISource
    "DroneShield Ltd"
    "DroneShield Breaks the Detection Paradigm: RfAI-3 Senses Drones That Have Never Been Seen Before"
    "DroneShield press release, Sydney"
    "2026"
    "https://www.droneshield.com/media/press-releases/droneshield-breaks-the-detection-paradigm-rfai-3-senses-drones-never-seen-before"
    Source.institutionalSource
    "vendor source for the product claim that RfAI-3 performs wideband RF sensing, distinguishes matched known emitters from previously unseen emissions, and reports a confidence assessment; not independent performance validation"
    Source.publicAttribution

droneShieldSensorFusionAI2023 : Source.AttributedSource
droneShieldSensorFusionAI2023 =
  Source.mkNoDOISource
    "DroneShield Ltd"
    "Launch of SensorFusionAI"
    "DroneShield press release"
    "2023"
    "https://www.droneshield.com/media/press-releases/launch-of-sensorfusionai-gx775"
    Source.institutionalSource
    "vendor source for the architecture claim that SensorFusionAI fuses RF, radar, acoustic and camera sensor outputs in a sensor-agnostic three-dimensional engine with confidence/threat assessment; not independent validation"
    Source.publicAttribution

droneShieldQ22026Release : Source.AttributedSource
droneShieldQ22026Release =
  Source.mkNoDOISource
    "DroneShield Ltd"
    "DroneShield Advances Decision Advantage with Q2 2026 Software Release as Drone Threats Scale Globally"
    "DroneShield software release, Sydney"
    "2026"
    "https://www.droneshield.com/media/press-releases/droneshield-advances-decision-advantage-with-q2-2026-software-release-as-drone-threats-scale-globally"
    Source.institutionalSource
    "vendor source for current DroneSentry-C2 / SensorFusionAI interoperability, fixed-wing classification, third-party radar support, and operator decision-layer claims; not a generic scientific theorem"
    Source.publicAttribution

droneShieldCapabilitiesSnapshot2026 : Source.AttributedSource
droneShieldCapabilitiesSnapshot2026 =
  Source.mkNoDOISource
    "DroneShield Ltd"
    "CUxS Capabilities"
    "DroneShield product capability page"
    "2026 snapshot"
    "https://www.droneshield.com/capabilities"
    Source.institutionalSource
    "vendor source mapping RfAI/RfAI-3, SensorFusionAI, command-and-control and electronic-warfare capability families; source identity does not create operational authority"
    Source.publicAttribution

acmaSection27CounterDrone2026 : Source.AttributedSource
acmaSection27CounterDrone2026 =
  Source.mkNoDOISource
    "Australian Communications and Media Authority"
    "Exemptions for banned equipment"
    "Australian Government / ACMA"
    "2026 snapshot"
    "https://www.acma.gov.au/exemptions-banned-equipment"
    Source.governmentSource
    "regulatory source for current section 27 exemption categories, including the Remotely Piloted Aircraft Disruption Determination authorising counter-drone equipment for specified Australian police use; this does not make detection, classification, vendor ownership, or purchase equivalent to legal authority to operate prohibited equipment"
    Source.publicAttribution

counterUASOperationalSources : List Source.AttributedSource
counterUASOperationalSources =
  droneShieldRfAI3Launch2026 ∷
  droneShieldSensorFusionAI2023 ∷
  droneShieldQ22026Release ∷
  droneShieldCapabilitiesSnapshot2026 ∷
  acmaSection27CounterDrone2026 ∷
  []

counterUASOperationalSourceAtlas : Source.AttributedSourceAtlas
counterUASOperationalSourceAtlas =
  Source.mkSourceAtlas
    "DroneShield and Australian counter-UAS operational sources"
    "DASHI.Applications.CounterUASOperationalSourceAtlasExact"
    counterUASOperationalSources
    "product-architecture and Australian regulatory provenance only; vendor claims do not become independent validation, academic review does not become product certification, and detection/threat evidence does not become legal authority"

counterUASOperationalSourceAtlasCreatesAuthority : Bool
counterUASOperationalSourceAtlasCreatesAuthority =
  Source.atlasCreatesAuthority counterUASOperationalSourceAtlas

counterUASOperationalSourceAtlasCreatesAuthorityIsFalse :
  counterUASOperationalSourceAtlasCreatesAuthority ≡ false
counterUASOperationalSourceAtlasCreatesAuthorityIsFalse =
  Source.atlasCreatesAuthorityIsFalse counterUASOperationalSourceAtlas

record CounterUASSourcePartitionBoundary : Set where
  constructor counterUASSourcePartitionBoundary
  field
    vendorClaimEqualsIndependentValidation : Bool
    vendorClaimEqualsIndependentValidationIsFalse :
      vendorClaimEqualsIndependentValidation ≡ false
    academicSOTAEqualsVendorProductCertification : Bool
    academicSOTAEqualsVendorProductCertificationIsFalse :
      academicSOTAEqualsVendorProductCertification ≡ false
    regulatoryExemptionEqualsThreatFinding : Bool
    regulatoryExemptionEqualsThreatFindingIsFalse :
      regulatoryExemptionEqualsThreatFinding ≡ false
    regulatoryExemptionEqualsUniversalPublicAuthority : Bool
    regulatoryExemptionEqualsUniversalPublicAuthorityIsFalse :
      regulatoryExemptionEqualsUniversalPublicAuthority ≡ false

canonicalCounterUASSourcePartitionBoundary : CounterUASSourcePartitionBoundary
canonicalCounterUASSourcePartitionBoundary =
  counterUASSourcePartitionBoundary
    false refl
    false refl
    false refl
    false refl
