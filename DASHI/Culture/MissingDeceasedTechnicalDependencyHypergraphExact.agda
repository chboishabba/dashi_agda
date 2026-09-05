module DASHI.Culture.MissingDeceasedTechnicalDependencyHypergraphExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TechnicalDependencyHypergraphExact as H

------------------------------------------------------------------------
-- Canonical technical nodes from the attribution atlas.
------------------------------------------------------------------------

anthonyChavez : H.TechnicalNode
anthonyChavez = H.technical-node H.personNode "Anthony Chavez"

darht : H.TechnicalNode
darht = H.technical-node H.facilityNode "Dual-Axis Radiographic Hydrodynamic Test (DARHT)"

scorpius : H.TechnicalNode
scorpius = H.technical-node H.programmeNode "Scorpius / Advanced Sources and Detectors"

subcriticalRadiography : H.TechnicalNode
subcriticalRadiography = H.technical-node H.technologyNode "multi-pulse x-ray radiography of subcritical experiments"

nuclearStockpileStewardship : H.TechnicalNode
nuclearStockpileStewardship = H.technical-node H.programmeNode "NNSA stockpile stewardship / subcritical experimentation"

joshuaLeBlanc : H.TechnicalNode
joshuaLeBlanc = H.technical-node H.personNode "Joshua LeBlanc"

spaceNuclearPropulsionIC : H.TechnicalNode
spaceNuclearPropulsionIC = H.technical-node H.technologyNode "space nuclear propulsion instrumentation and controls"

fissionSurfacePower : H.TechnicalNode
fissionSurfacePower = H.technical-node H.programmeNode "NASA 40 kW Fission Surface Power technology maturation"

monicaReza : H.TechnicalNode
monicaReza = H.technical-node H.personNode "Monica Jacinto / Monica Reza"

burnResistantAlloys : H.TechnicalNode
burnResistantAlloys = H.technical-node H.technologyNode "burn-resistant high-strength nickel-based alloys for oxygen-rich environments"

alloyPatent : H.TechnicalNode
alloyPatent = H.technical-node H.publicationOrPatentNode "US20040208777A1 / US10/769,195"

williamMcCasland : H.TechnicalNode
williamMcCasland = H.technical-node H.personNode "William N. McCasland"

afrlSpaceVehicles : H.TechnicalNode
afrlSpaceVehicles = H.technical-node H.programmeNode "AFRL Space Vehicles Directorate"

spaceBasedLaser : H.TechnicalNode
spaceBasedLaser = H.technical-node H.programmeNode "Space Based Laser Project Office"

navstarGPS : H.TechnicalNode
navstarGPS = H.technical-node H.programmeNode "Navstar GPS Joint Program Office"

nunoLoureiro : H.TechnicalNode
nunoLoureiro = H.technical-node H.personNode "Nuno F. G. Loureiro"

magneticReconnection : H.TechnicalNode
magneticReconnection = H.technical-node H.technologyNode "magnetic reconnection / strongly magnetized plasma dynamics"

fusionPlasma : H.TechnicalNode
fusionPlasma = H.technical-node H.programmeNode "fusion plasma confinement and transport research"

fusionSpacePropulsionEngineering : H.TechnicalNode
fusionSpacePropulsionEngineering = H.technical-node H.technologyNode "fusion/plasma engineering interface for space propulsion"

michaelHicks : H.TechnicalNode
michaelHicks = H.technical-node H.personNode "Michael David Hicks"

planetaryDefense : H.TechnicalNode
planetaryDefense = H.technical-node H.programmeNode "DART / near-Earth-object planetary science"

frankMaiwald : H.TechnicalNode
frankMaiwald = H.technical-node H.personNode "Frank W. Maiwald"

planetaryMassSpectrometry : H.TechnicalNode
planetaryMassSpectrometry = H.technical-node H.technologyNode "planetary mass spectrometry / biosignature action spectroscopy"

carlGrillmair : H.TechnicalNode
carlGrillmair = H.technical-node H.personNode "Carl J. Grillmair"

stellarStreams : H.TechnicalNode
stellarStreams = H.technical-node H.technologyNode "stellar streams / Galactic structure / dark-matter probing"

jpl : H.TechnicalNode
jpl = H.technical-node H.institutionNode "NASA Jet Propulsion Laboratory"

caltechIPAC : H.TechnicalNode
caltechIPAC = H.technical-node H.institutionNode "Caltech/IPAC"

------------------------------------------------------------------------
-- Strong person-to-work / programme edges.
------------------------------------------------------------------------

chavezScorpius : H.TechnicalHyperedge
chavezScorpius = H.technical-hyperedge
  (anthonyChavez ∷ scorpius ∷ [])
  H.workedOn H.primaryRoleReceipt
  "LANL National Security Science, Summer 2025, Anthony Chavez profile"
  "LANL states that Chavez completed design work for the Scorpius accelerator."

chavezDARHT : H.TechnicalHyperedge
chavezDARHT = H.technical-hyperedge
  (anthonyChavez ∷ darht ∷ [])
  H.workedOn H.primaryRoleReceipt
  "LANL National Security Science, Summer 2025"
  "LANL states that Chavez worked more than 25 years at DARHT."

scorpiusRadiography : H.TechnicalHyperedge
scorpiusRadiography = H.technical-hyperedge
  (scorpius ∷ subcriticalRadiography ∷ nuclearStockpileStewardship ∷ [])
  H.programmeUsesTechnology H.officialProgrammeReceipt
  "LANL / NNSA technical descriptions of Scorpius"
  "Scorpius is a multi-pulse electron linear accelerator for x-ray radiography of subcritical experiments in stockpile stewardship."

leblancSpaceNuclear : H.TechnicalHyperedge
leblancSpaceNuclear = H.technical-hyperedge
  (joshuaLeBlanc ∷ spaceNuclearPropulsionIC ∷ fissionSurfacePower ∷ [])
  H.workedOn H.primaryRoleReceipt
  "NASA NTRS 20250008475"
  "NASA names LeBlanc as author and Space Nuclear Propulsion I&C TechMat Team Lead in the fission surface power instrumentation/control context."

rezaAlloyPatent : H.TechnicalHyperedge
rezaAlloyPatent = H.technical-hyperedge
  (monicaReza ∷ burnResistantAlloys ∷ alloyPatent ∷ [])
  H.authoredOrInvented H.primaryTechnicalReceipt
  "US20040208777A1 / US10/769,195"
  "Patent names Monica A. Jacinto and Dallis Ann Hardwick as inventors of burn-resistant/high-strength alloys for oxygen-rich structural environments."

mccaslandSpaceVehicles : H.TechnicalHyperedge
mccaslandSpaceVehicles = H.technical-hyperedge
  (williamMcCasland ∷ afrlSpaceVehicles ∷ [])
  H.ledOrDirected H.primaryRoleReceipt
  "U.S. Air Force official biography"
  "McCasland served as materiel wing director, AFRL Space Vehicles Directorate, and commander, Phillips Research Site."

mccaslandSpaceLaser : H.TechnicalHyperedge
mccaslandSpaceLaser = H.technical-hyperedge
  (williamMcCasland ∷ spaceBasedLaser ∷ [])
  H.ledOrDirected H.primaryRoleReceipt
  "U.S. Air Force official biography"
  "McCasland served as System Program Director, Space Based Laser Project Office."

mccaslandGPS : H.TechnicalHyperedge
mccaslandGPS = H.technical-hyperedge
  (williamMcCasland ∷ navstarGPS ∷ [])
  H.ledOrDirected H.primaryRoleReceipt
  "U.S. Air Force official biography"
  "McCasland served as Chief Engineer, Navstar GPS Joint Program Office."

loureiroPlasma : H.TechnicalHyperedge
loureiroPlasma = H.technical-hyperedge
  (nunoLoureiro ∷ magneticReconnection ∷ fusionPlasma ∷ [])
  H.workedOn H.primaryTechnicalReceipt
  "MIT Physics / PSFC profile; Viriato DOI 10.1016/j.cpc.2016.05.004"
  "Loureiro's documented work includes magnetic reconnection, magnetized plasma dynamics, turbulence, fusion confinement and transport."

fusionSpaceDocumentedBridge : H.TechnicalHyperedge
fusionSpaceDocumentedBridge = H.technical-hyperedge
  (fusionPlasma ∷ fusionSpacePropulsionEngineering ∷ [])
  H.documentedTechnologyDomainBridge H.officialProgrammeReceipt
  "NASA NTRS, 'Fusion for Space Propulsion' and NASA fusion-propulsion concept studies"
  "NASA explicitly documents that plasma/fusion physics, enabling component technologies, computation and diagnostics form an engineering base for fusion space-propulsion research. This establishes a domain bridge, not Loureiro participation in a NASA propulsion programme."

hicksPlanetary : H.TechnicalHyperedge
hicksPlanetary = H.technical-hyperedge
  (michaelHicks ∷ planetaryDefense ∷ [])
  H.workedOn H.primaryRoleReceipt
  "JPL Family News / University of Arizona memorial"
  "Hicks worked on comet/asteroid physical properties and named mission science teams including DART and NEAT."

maiwaldPlanetary : H.TechnicalHyperedge
maiwaldPlanetary = H.technical-hyperedge
  (frankMaiwald ∷ planetaryMassSpectrometry ∷ [])
  H.workedOn H.primaryRoleReceipt
  "JPL Principal registry / JPL SURP 2023"
  "Maiwald's documented work is planetary mass spectrometry and biosignature action spectroscopy."

grillmairStreams : H.TechnicalHyperedge
grillmairStreams = H.technical-hyperedge
  (carlGrillmair ∷ stellarStreams ∷ [])
  H.workedOn H.primaryTechnicalReceipt
  "Caltech/IPAC CV; DOI 10.3847/1538-4357/aa8872"
  "Grillmair's documented work is stellar streams, Galactic structure and dark-matter probing."

------------------------------------------------------------------------
-- Weak edges deliberately quotiented out.
------------------------------------------------------------------------

hicksMaiwaldJPLOnly : H.TechnicalHyperedge
hicksMaiwaldJPLOnly = H.technical-hyperedge
  (michaelHicks ∷ frankMaiwald ∷ jpl ∷ [])
  H.sameInstitutionOnly H.primaryRoleReceipt
  "JPL affiliation records"
  "Both worked at JPL; no shared project is inferred from common employer alone."

rezaHicksJPLOnly : H.TechnicalHyperedge
rezaHicksJPLOnly = H.technical-hyperedge
  (monicaReza ∷ michaelHicks ∷ jpl ∷ [])
  H.sameInstitutionOnly H.boundedSecondaryReceipt
  "separate JPL role records"
  "Institutional overlap only; no same-project receipt encoded."

rezaMaiwaldJPLOnly : H.TechnicalHyperedge
rezaMaiwaldJPLOnly = H.technical-hyperedge
  (monicaReza ∷ frankMaiwald ∷ jpl ∷ [])
  H.sameInstitutionOnly H.boundedSecondaryReceipt
  "separate JPL role records"
  "Institutional overlap only; no same-project receipt encoded."

grillmairJPLFamilyOnly : H.TechnicalHyperedge
grillmairJPLFamilyOnly = H.technical-hyperedge
  (carlGrillmair ∷ caltechIPAC ∷ jpl ∷ [])
  H.sameInstitutionalFamilyOnly H.primaryRoleReceipt
  "Caltech/IPAC and JPL institutional relationship"
  "Caltech/IPAC and JPL share institutional ecosystem; this alone is not a technical dependency."

rezaMcCaslandReported : H.TechnicalHyperedge
rezaMcCaslandReported = H.technical-hyperedge
  (monicaReza ∷ williamMcCasland ∷ [])
  H.reportedRelationshipOnly H.mediaNarrativeReceipt
  "House Oversight letter repeats public-report allegation"
  "Reported professional relationship is retained as a lead but erased by the technical quotient until primary programme/personnel evidence is recovered."

------------------------------------------------------------------------
-- Candidate adjacencies.  The generic fusion<->space engineering bridge is now
-- source-backed; the unresolved question is whether Loureiro's particular work
-- entered a specific space-propulsion lineage or observer surface.
------------------------------------------------------------------------

nuclearSystemsAdjacency : H.CandidateDomainAdjacency
nuclearSystemsAdjacency = H.candidate-domain-adjacency
  scorpius
  fissionSurfacePower
  "nuclear systems engineering"
  "real domain adjacency; no shared programme/contract/personnel dependency presently established"
  "recover programme contracts, cross-lab personnel, common suppliers, or explicit technology-transfer records"

spaceMaterialsAdjacency : H.CandidateDomainAdjacency
spaceMaterialsAdjacency = H.candidate-domain-adjacency
  burnResistantAlloys
  afrlSpaceVehicles
  "aerospace materials / military space systems"
  "technically compatible adjacency; no primary receipt presently ties Reza's alloy patent to McCasland's Space Vehicles programmes"
  "recover Air Force funding award, contract number, programme document, or named joint project personnel"

plasmaNuclearAdjacency : H.CandidateDomainAdjacency
plasmaNuclearAdjacency = H.candidate-domain-adjacency
  magneticReconnection
  fusionSpacePropulsionEngineering
  "fusion/plasma physics <-> space propulsion"
  "generic engineering-domain bridge is source-backed by NASA; Loureiro-specific participation/transfer remains unresolved"
  "recover a Loureiro-specific grant, advisory role, workshop, technology-transfer, publication, contractor, programme or technical-intelligence observer receipt if one exists"

planetarySensingAdjacency : H.CandidateDomainAdjacency
planetarySensingAdjacency = H.candidate-domain-adjacency
  planetaryDefense
  planetaryMassSpectrometry
  "planetary science / sensing"
  "same broad JPL science domain, but distinct documented mission/instrument work"
  "locate shared mission, instrument, proposal, team roster or publication before promoting to technical intersection"

------------------------------------------------------------------------
-- Exact quotient regressions.
------------------------------------------------------------------------

hicksMaiwaldInstitutionEdgeErased :
  H.quotientDisposition hicksMaiwaldJPLOnly ≡ H.erasedAsInstitutionOnly
hicksMaiwaldInstitutionEdgeErased = refl

rezaMcCaslandReportedEdgeErased :
  H.quotientDisposition rezaMcCaslandReported ≡ H.erasedAsReportedRelationshipOnly
rezaMcCaslandReportedEdgeErased = refl

chavezScorpiusSurvives :
  H.quotientDisposition chavezScorpius ≡ H.survivesTechnicalQuotient
chavezScorpiusSurvives = refl

rezaPatentSurvives :
  H.quotientDisposition rezaAlloyPatent ≡ H.survivesTechnicalQuotient
rezaPatentSurvives = refl

fusionSpaceBridgeSurvives :
  H.quotientDisposition fusionSpaceDocumentedBridge ≡ H.survivesTechnicalQuotient
fusionSpaceBridgeSurvives = refl

record CurrentTechnicalIntersectionAssessment : Set where
  constructor current-technical-intersection-assessment
  field
    oneUnifiedCrossRosterProgrammeEstablished : Bool
    oneUnifiedCrossRosterProgrammeEstablishedIsFalse :
      oneUnifiedCrossRosterProgrammeEstablished ≡ false

    strongWithinPersonWorkEdgesSurvive : Bool
    strongWithinPersonWorkEdgesSurviveIsTrue :
      strongWithinPersonWorkEdgesSurvive ≡ true

    documentedFusionSpaceDomainBridgeEstablished : Bool
    documentedFusionSpaceDomainBridgeEstablishedIsTrue :
      documentedFusionSpaceDomainBridgeEstablished ≡ true

    documentedFusionSpaceBridgeMeansLoureiroWorkedOnSpacePropulsion : Bool
    documentedFusionSpaceBridgeMeansLoureiroWorkedOnSpacePropulsionIsFalse :
      documentedFusionSpaceBridgeMeansLoureiroWorkedOnSpacePropulsion ≡ false

    institutionOnlyEdgesSurvive : Bool
    institutionOnlyEdgesSurviveIsFalse : institutionOnlyEdgesSurvive ≡ false

    mediaOnlyEdgesSurvive : Bool
    mediaOnlyEdgesSurviveIsFalse : mediaOnlyEdgesSurvive ≡ false

    personSpecificAdjacenciesRemainAcquisitionTargets : Bool
    personSpecificAdjacenciesRemainAcquisitionTargetsIsTrue :
      personSpecificAdjacenciesRemainAcquisitionTargets ≡ true

canonicalCurrentTechnicalIntersectionAssessment : CurrentTechnicalIntersectionAssessment
canonicalCurrentTechnicalIntersectionAssessment =
  current-technical-intersection-assessment
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
