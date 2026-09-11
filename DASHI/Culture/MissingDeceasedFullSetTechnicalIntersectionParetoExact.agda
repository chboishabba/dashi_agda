module DASHI.Culture.MissingDeceasedFullSetTechnicalIntersectionParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.ScientificRosterWorkCoverageExact as US
import DASHI.Culture.ChineseStrategicScientistRosterSnowballExact as China
import DASHI.Culture.MissingDeceasedTechnicalIntersectionAcquisitionExact as Acquire
import DASHI.Culture.NASAFusionPlasmaSpacePropulsionBridgeExact as Fusion
import DASHI.Physics.Materials.FusionPropulsionMaterialSurvivabilityCrossPollinationExact as Materials
import DASHI.Core.NDimParetoHyperfabricExact as Pareto

------------------------------------------------------------------------
-- FULL-SET TECHNICAL-INTERSECTION PARETO ATLAS
--
-- This is a navigation/proof-search owner, not a common-cause theorem.  Every
-- retained person gets a row whose technical work remains source-owned by the
-- relevant domain module.  Cross-domain adjacency nominates acquisitions only.
------------------------------------------------------------------------

data IntersectionStrength : Set where
  exactWorkObject
  programmeBackedDomainBridge
  domainAdjacencyOnly
  roleCapabilityOnly
  identityWeldPending : IntersectionStrength

record FullSetTechnicalIntersection : Set where
  constructor full-set-technical-intersection
  field
    person : String
    cohort : String
    retainedWork : String
    strongestIntersection : String
    strength : IntersectionStrength
    paidKernel : String
    unpaidBridge : String
    nextDiscriminatingReceipt : String
    commonCausePaid : Bool

open FullSetTechnicalIntersection public

------------------------------------------------------------------------
-- U.S. retained roster.
------------------------------------------------------------------------

loureiroFusionPlasmaRow : FullSetTechnicalIntersection
loureiroFusionPlasmaRow = full-set-technical-intersection
  "Nuno F. G. Loureiro" "US"
  "KREHM/KRMHD, magnetic reconnection, plasmoid and kinetic plasma physics"
  "fusion/magnetized-plasma physics <-> NASA fusion-space propulsion domain"
  programmeBackedDomainBridge
  "NASA Fusion Driven Rocket / Direct Fusion Drive establish the domain bridge independently of Loureiro"
  "no named Loureiro participation in a NASA fusion-propulsion programme is paid"
  "grant/contract/advisory/review/technology-transfer object naming Loureiro or his exact work in a fusion-space programme"
  false

leblancNuclearPowerRow : FullSetTechnicalIntersection
leblancNuclearPowerRow = full-set-technical-intersection
  "Joshua Kyle LeBlanc" "US"
  "Fission Surface Power instrumentation and controls"
  "space nuclear power <-> advanced nuclear/fusion propulsion systems engineering"
  domainAdjacencyOnly
  "exact NASA FSP I&C work is owned"
  "no shared fusion-propulsion programme/personnel/supplier object is paid"
  "post-loss SNP I&C roster plus any shared nuclear-propulsion technology-transfer or supplier object"
  false

rezaOxygenMaterialsRow : FullSetTechnicalIntersection
rezaOxygenMaterialsRow = full-set-technical-intersection
  "Monica Jacinto Reza" "US"
  "burn-resistant high-strength nickel superalloy for oxygen-rich rocket environments"
  "rocket-material survivability <-> fusion-propulsion material survivability"
  exactWorkObject
  "patent chemistry/process, gamma/gamma-prime mechanism and NASA MSFC oxygen-rich assessment"
  "oxygen-rich chemical-rocket material is not thereby a fusion-plasma or metamaterial object"
  "exact programme/material-transfer receipt if Reza/Mondaloy is claimed in fusion, metamaterial or classified-propulsion lineage"
  false

maiwaldSpectroscopyRow : FullSetTechnicalIntersection
maiwaldSpectroscopyRow = full-set-technical-intersection
  "Frank W. Maiwald" "US"
  "cryogenic ion action spectroscopy and quadrupole ion-trap mass spectrometry"
  "planetary/terrestrial molecular discrimination <-> alleged classified sample-analysis narrative"
  exactWorkObject
  "JPL/CU spectroscopy method, platform and project continuity are paid"
  "no NHI/craft-retrieval sample, secure deployment or classified-sample custody object is paid"
  "instrument deployment log, sample manifest, funding/work-package or secure-facility same-object record"
  false

mccaslandSystemsRow : FullSetTechnicalIntersection
mccaslandSystemsRow = full-set-technical-intersection
  "William Neil McCasland" "US"
  "fault-tolerant flexible-structure control and later aerospace/programme leadership"
  "advanced aerospace programme management <-> materials/propulsion acquisition hypotheses"
  domainAdjacencyOnly
  "control work and later institutional programme roles are source-backed"
  "Reza/Mondaloy or fusion-propulsion same-programme edge remains unpaid"
  "dated DBE/AFRL programme, award, contract or team object joining the same technical programme"
  false

gillmairAstrophysicsRow : FullSetTechnicalIntersection
gillmairAstrophysicsRow = full-set-technical-intersection
  "Carl J. Grillmair" "US"
  "stellar streams and Galactic-potential inference"
  "astrophysical inverse problems <-> no paid propulsion/material intersection"
  exactWorkObject
  "public astronomy work is paid"
  "technical removal/common-programme bridge absent"
  "event-state and matched-control continuity only; do not force an exotic-tech intersection"
  false

hicksPlanetaryRow : FullSetTechnicalIntersection
hicksPlanetaryRow = full-set-technical-intersection
  "Michael David Hicks" "US"
  "small-body/comet photometry and planetary inference"
  "planetary science <-> Maiwald planetary-analysis domain"
  domainAdjacencyOnly
  "both domains are JPL/planetary but scientifically distinct"
  "no shared mission/instrument/proposal object naming both is paid"
  "shared mission, instrument, proposal or publication if one exists"
  false

chavezAcceleratorRow : FullSetTechnicalIntersection
chavezAcceleratorRow = full-set-technical-intersection
  "Anthony Chavez identities" "US"
  "candidate DARHT/Scorpius engineering and separate spectrometer-calibration work"
  "pulsed-power/accelerator engineering <-> advanced energy/nuclear systems"
  identityWeldPending
  "technical owners exist for institutional/publication identities"
  "missing-person identity is not yet welded to those technical identities"
  "same-person primary receipt before any programme intersection is inherited"
  false

thomasBiologyRow : FullSetTechnicalIntersection
thomasBiologyRow = full-set-technical-intersection
  "Jason R. Thomas" "US"
  "STING signalling and ferritinophagy chemical biology"
  "biological/chemical mechanism science <-> no paid aerospace programme intersection"
  exactWorkObject
  "mechanism work is paid"
  "no common technical programme is paid"
  "event-state/continuity controls rather than forced aerospace adjacency"
  false

amyExoticGravityRow : FullSetTechnicalIntersection
amyExoticGravityRow = full-set-technical-intersection
  "Amy Eskridge" "US"
  "engineered inertial/gravitational mechanism families and POAMS review/custody investigation"
  "antigravity/vacuum-thrust hypotheses <-> historical NASA fusion/TWDEC quantum-vacuum wording"
  domainAdjacencyOnly
  "typed antigravity consumers plus official NASA TechPort historical Quantum Vacuum thruster mention"
  "no same-object bridge from Amy to TechPort 12110 or an operational vacuum-thrust device is paid"
  "named programme/person/object lineage, apparatus receipt and validated thrust discriminator"
  false

casiasAdminRow : FullSetTechnicalIntersection
casiasAdminRow = full-set-technical-intersection
  "Melissa Casias" "US"
  "reported LANL administrative role"
  "information-routing/personnel/badge visibility"
  roleCapabilityOnly
  "role is retained without manufacturing scientific work"
  "clearance, specific programme visibility and intelligence-cleanup claim remain unpaid"
  "primary duty/access/badge-routing records plus event/forensic carrier"
  false

garciaCustodianRow : FullSetTechnicalIntersection
garciaCustodianRow = full-set-technical-intersection
  "Steven Abel Garcia" "US"
  "reported property-custodian role"
  "inventory/property-accountability visibility"
  roleCapabilityOnly
  "missing-person identity is paid; technical possession is not"
  "specific asset anomaly, metamaterial transfer or black-program inventory edge remains unpaid"
  "primary employer duty scope, asset/accountability record and event-time assignment"
  false

sullivanIntelligenceRow : FullSetTechnicalIntersection
sullivanIntelligenceRow = full-set-technical-intersection
  "Matthew James Sullivan" "US"
  "former U.S. Air Force intelligence role"
  "intelligence visibility <-> later UAP/crash-retrieval claims"
  roleCapabilityOnly
  "service-role carrier retained separately from later claims"
  "anonymous/secondary UAP claims do not pay programme participation"
  "primary event-time programme/testimony/service object if public"
  false

------------------------------------------------------------------------
-- Chinese named roster.
------------------------------------------------------------------------

chenMicroelectronicsRow : FullSetTechnicalIntersection
chenMicroelectronicsRow = full-set-technical-intersection
  "Chen Shuming" "China"
  "military DSP/flight-control processor and microelectronics work"
  "strategic compute hardware <-> autonomous/AI systems"
  exactWorkObject
  "NUDT work identity paid"
  "event carrier and exact post-loss project succession remain incomplete"
  "primary event object plus chip/project successor/custody object"
  false

fengStrategicGameRow : FullSetTechnicalIntersection
fengStrategicGameRow = full-set-technical-intersection
  "Feng Yanghe" "China"
  "War Skull II wargaming, Bayesian classification and noisy-label ML"
  "strategic game/AI/statistics <-> adversarial proof-search methodology"
  exactWorkObject
  "NUDT and publisher work objects paid"
  "event cause and post-loss programme/agent custody not yet paid"
  "primary event object plus first post-loss War Skull/project/role carrier"
  false

zhouPolymerRow : FullSetTechnicalIntersection
zhouPolymerRow = full-set-technical-intersection
  "Zhou Guangyuan" "China"
  "high-temperature polyimide aerogel/materials"
  "thermal materials <-> extreme-environment aerospace/material survivability"
  exactWorkObject
  "DICP work and DOI 10.1016/j.cej.2023.147642 paid"
  "exact event and application/succession lineage remain incomplete"
  "primary event object plus technology-transfer/project successor"
  false

liuSecurityRow : FullSetTechnicalIntersection
liuSecurityRow = full-set-technical-intersection
  "Liu Donghao" "China"
  "data-security governance / DSMM implementation"
  "security-governance <-> information-routing/custody hypothesis"
  exactWorkObject
  "institutional work identity plus obituary-derived event identity substantially welded"
  "independent forensic cause and post-loss programme succession remain unpaid"
  "independent event carrier plus first successor/role/project object"
  false

zhangXiaoxinSpaceWeatherRow : FullSetTechnicalIntersection
zhangXiaoxinSpaceWeatherRow = full-set-technical-intersection
  "Zhang Xiaoxin" "China"
  "space-weather monitoring, forecasting and Fengyun applications"
  "sensing/warning systems <-> strategic space-domain continuity"
  exactWorkObject
  "space-weather work and obituary-derived event identity substantially welded"
  "independent cause carrier and programme succession remain unpaid"
  "first post-loss role/project/payload custody object"
  false

zhangDaibingAutonomyRow : FullSetTechnicalIntersection
zhangDaibingAutonomyRow = full-set-technical-intersection
  "Zhang Daibing" "China"
  "UAV autonomous landing, carrier landing and formation control"
  "autonomous control <-> strategic game/AI and aerospace control"
  exactWorkObject
  "multiple DOI-level control publications paid"
  "primary event and post-NUDT company/project custody remain unpaid"
  "primary event record plus successor/company/project ownership carrier"
  false

liMinyongChemistryRow : FullSetTechnicalIntersection
liMinyongChemistryRow = full-set-technical-intersection
  "Li Minyong" "China"
  "photocontrolled drug discovery and disease-target visualisation"
  "molecular control/imaging <-> analytical/spectroscopy domain only at broad method level"
  exactWorkObject
  "Hainan institutional work identity paid"
  "no Maiwald same-method/project object or strategic common programme is paid"
  "primary event plus exact project/patent/publication succession"
  false

fangMetamaterialRow : FullSetTechnicalIntersection
fangMetamaterialRow = full-set-technical-intersection
  "Fang Daining" "China"
  "active mechanical metamaterials, multifield materials and extreme-temperature testing"
  "architected metamaterials <-> propulsion/material survivability"
  exactWorkObject
  "DOI 10.1002/advs.202102662 and BIT material-science programme are paid"
  "no same-object connection to Mondaloy, S4, fusion propulsion or recovered material is paid"
  "primary event plus post-loss project/lab/custody object; any cross-programme claim needs exact provenance"
  false

yanHypersonicRow : FullSetTechnicalIntersection
yanHypersonicRow = full-set-technical-intersection
  "Yan Hong" "China"
  "Mach-5 thermal-excitation flow control and plasma actuators"
  "hypersonic/plasma flow control <-> plasma/propulsion domain"
  exactWorkObject
  "NPU work identity and DOI-level flow-control objects are paid"
  "fusion-propulsion same-object edge is not paid; event cause remains source-bounded"
  "post-loss NPU project/role/custody object plus independent event/cause carrier"
  false

------------------------------------------------------------------------
-- Reuse boundaries and preserve proof-search semantics.
------------------------------------------------------------------------

existingParetoBoundary : Pareto.NDimParetoHyperfabricBoundary
existingParetoBoundary = Pareto.canonicalNDimParetoHyperfabricBoundary

existingTechnicalAcquisitionBoundary : Acquire.TechnicalIntersectionAcquisitionBoundary
existingTechnicalAcquisitionBoundary = Acquire.canonicalTechnicalIntersectionAcquisitionBoundary

fusionDomainBridgeExists : Fusion.fusionToPropulsionPromoted ≡ Fusion.fusionToPropulsionPromoted
fusionDomainBridgeExists = refl

materialCrossPollinationExists : Materials.canonicalFusionMaterialBoundary ≡ Materials.canonicalFusionMaterialBoundary
materialCrossPollinationExists = refl

technicalAdjacencyDoesNotCreateSharedProgramme : Bool
technicalAdjacencyDoesNotCreateSharedProgramme = true

fullSetRowsDoNotCreateCommonCause : Bool
fullSetRowsDoNotCreateCommonCause = true

record FullSetIntersectionBoundary : Set where
  constructor full-set-intersection-boundary
  field
    everyPersonMustShareOneTechnicalDomain : Bool
    domainBridgeCreatesPersonProgrammeEdge : Bool
    roleCapabilityCreatesScientificAuthorship : Bool
    crossNationalSimilarityCreatesCommonCause : Bool
    sourceBackedIntersectionMayPrioritiseAcquisition : Bool
    sameObjectStillRequiredForPromotion : Bool

canonicalFullSetIntersectionBoundary : FullSetIntersectionBoundary
canonicalFullSetIntersectionBoundary = full-set-intersection-boundary
  false false false false true true
