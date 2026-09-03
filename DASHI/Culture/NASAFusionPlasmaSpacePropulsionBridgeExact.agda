module DASHI.Culture.NASAFusionPlasmaSpacePropulsionBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.TechnicalDependencyHypergraphExact as H
import DASHI.Core.ProgrammeMediatedTechnicalDomainBridgeBidiExact as B

------------------------------------------------------------------------
-- NASA PROGRAMME-LEVEL FUSION / MAGNETIZED-PLASMA / SPACE-PROPULSION
-- BRIDGE.
--
-- Source discipline:
--   * NASA TechPort project 4365 / Fusion Driven Rocket.
--   * NASA TechPort project 93869 / Direct Fusion Drive architecture.
--   * NASA TechPort project 4373 / Aneutronic Fusion Spacecraft Architecture.
--
-- These receipts establish a technology-domain bridge. They do not establish
-- that any named person in another fixture worked on these projects.
------------------------------------------------------------------------

fusionDrivenRocket : H.TechnicalNode
fusionDrivenRocket = H.technical-node H.programmeNode
  "NASA NIAC Fusion Driven Rocket / direct conversion of fusion energy"

magnetizedFusionPlasma : H.TechnicalNode
magnetizedFusionPlasma = H.technical-node H.technologyNode
  "magnetized plasma compressed and heated to fusion conditions"

magneticNozzlePropulsion : H.TechnicalNode
magneticNozzlePropulsion = H.technical-node H.technologyNode
  "hot plasma / propellant expansion through a magnetic nozzle for spacecraft thrust"

fieldReversedConfiguration : H.TechnicalNode
fieldReversedConfiguration = H.technical-node H.technologyNode
  "field-reversed configuration (FRC) fusion plasma"

directFusionDrive : H.TechnicalNode
directFusionDrive = H.technical-node H.programmeNode
  "NASA Direct Fusion Drive / fusion-enabled outer-planet spacecraft architecture"

aneutronicFusionSpacecraft : H.TechnicalNode
aneutronicFusionSpacecraft = H.technical-node H.programmeNode
  "NASA Aneutronic Fusion Spacecraft Architecture"

fusionProductsDirectThrust : H.TechnicalNode
fusionProductsDirectThrust = H.technical-node H.technologyNode
  "direct propulsive thrust from fusion products / fusion-powered plasma propulsion"

------------------------------------------------------------------------
-- Same-programme technical receipts.
------------------------------------------------------------------------

fusionDrivenRocketReceipt : H.TechnicalHyperedge
fusionDrivenRocketReceipt = H.technical-hyperedge
  (fusionDrivenRocket ∷ magnetizedFusionPlasma ∷ magneticNozzlePropulsion ∷ [])
  H.programmeUsesTechnology
  H.officialProgrammeReceipt
  "NASA TechPort project 4365; Fusion Driven Rocket / Nuclear Propulsion through Direct Conversion of Fusion Energy"
  "NASA describes propellant compressing and heating a magnetized plasma to fusion conditions, with released fusion energy heating the propellant and a magnetic nozzle converting that energy into propulsive and electrical energy."

directFusionDriveReceipt : H.TechnicalHyperedge
directFusionDriveReceipt = H.technical-hyperedge
  (directFusionDrive ∷ fieldReversedConfiguration ∷ magneticNozzlePropulsion ∷ [])
  H.programmeUsesTechnology
  H.officialProgrammeReceipt
  "NASA TechPort project 93869; Fusion-Enabled Pluto Orbiter and Lander"
  "NASA describes Direct Fusion Drive as based on the Princeton Field-Reversed Configuration fusion reactor and as providing integrated spacecraft propulsion and power, including thrust from plasma expanding through a magnetic nozzle."

aneutronicFusionReceipt : H.TechnicalHyperedge
aneutronicFusionReceipt = H.technical-hyperedge
  (aneutronicFusionSpacecraft ∷ fusionProductsDirectThrust ∷ magneticNozzlePropulsion ∷ [])
  H.programmeUsesTechnology
  H.officialProgrammeReceipt
  "NASA TechPort project 4373; Aneutronic Fusion Spacecraft Architecture"
  "NASA describes neutron-free fusion as the primary energy source, with a beam-conditioning/nozzle concept producing useful propulsive thrust directly from fusion products and some energy converted to electricity."

fusionDrivenRocketSurvives :
  H.quotientDisposition fusionDrivenRocketReceipt ≡ H.survivesTechnicalQuotient
fusionDrivenRocketSurvives = refl

directFusionDriveSurvives :
  H.quotientDisposition directFusionDriveReceipt ≡ H.survivesTechnicalQuotient
directFusionDriveSurvives = refl

aneutronicFusionSurvives :
  H.quotientDisposition aneutronicFusionReceipt ≡ H.survivesTechnicalQuotient
aneutronicFusionSurvives = refl

------------------------------------------------------------------------
-- BIDI programme-domain bridges. The first refl pins the literal endpoints.
------------------------------------------------------------------------

fusionToPropulsionBridge : B.ProgrammeDomainBridge
fusionToPropulsionBridge = B.programme-domain-bridge
  fusionDrivenRocket
  magnetizedFusionPlasma
  magneticNozzlePropulsion
  fusionDrivenRocketReceipt
  refl
  refl
  refl
  refl
  "NASA TechPort project 4365"
  "Fusion/magnetized-plasma physics and spacecraft propulsion are joined by one official NASA programme description; this is stronger than domain similarity."

frcToPropulsionBridge : B.ProgrammeDomainBridge
frcToPropulsionBridge = B.programme-domain-bridge
  directFusionDrive
  fieldReversedConfiguration
  magneticNozzlePropulsion
  directFusionDriveReceipt
  refl
  refl
  refl
  refl
  "NASA TechPort project 93869"
  "A field-reversed-configuration fusion object is explicitly reused in an integrated spacecraft propulsion-and-power architecture."

aneutronicToPropulsionBridge : B.ProgrammeDomainBridge
aneutronicToPropulsionBridge = B.programme-domain-bridge
  aneutronicFusionSpacecraft
  fusionProductsDirectThrust
  magneticNozzlePropulsion
  aneutronicFusionReceipt
  refl
  refl
  refl
  refl
  "NASA TechPort project 4373"
  "Aneutronic fusion products are explicitly coupled to a spacecraft-thrust architecture."

fusionToPropulsionPromoted : B.PromotedTechnicalDomainBridge
fusionToPropulsionPromoted = B.promote fusionToPropulsionBridge

frcToPropulsionPromoted : B.PromotedTechnicalDomainBridge
frcToPropulsionPromoted = B.promote frcToPropulsionBridge

------------------------------------------------------------------------
-- Reconnection/FRC precision firewall.
--
-- Magnetic reconnection is a genuine neighbouring plasma-physics coordinate,
-- but the NASA programme receipts above do not identify propulsion itself with
-- magnetic reconnection. FRC/magnetized-plasma topology is the stronger
-- same-object bridge presently owned here.
------------------------------------------------------------------------

record ReconnectionPrecisionBoundary : Set where
  constructor reconnection-precision-boundary
  field
    magneticReconnectionIsIdenticalToFRCPropulsion : Bool
    magneticReconnectionIsIdenticalToFRCPropulsionIsFalse :
      magneticReconnectionIsIdenticalToFRCPropulsion ≡ false

    frcMagnetizedPlasmaIsProgrammeLevelBridge : Bool
    frcMagnetizedPlasmaIsProgrammeLevelBridgeIsTrue :
      frcMagnetizedPlasmaIsProgrammeLevelBridge ≡ true

canonicalReconnectionPrecisionBoundary : ReconnectionPrecisionBoundary
canonicalReconnectionPrecisionBoundary =
  reconnection-precision-boundary false refl true refl
