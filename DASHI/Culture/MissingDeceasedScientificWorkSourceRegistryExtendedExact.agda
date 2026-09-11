module DASHI.Culture.MissingDeceasedScientificWorkSourceRegistryExtendedExact where

------------------------------------------------------------------------
-- EXTENDED SOURCE COVERAGE + SNOWBALL COORDINATES
--
-- Citation/provenance remains authoritative for evidentiary claims.  QID and
-- Dewey coordinates are traversal/search coordinates only: they never create
-- person identity, same-object identity, theorem authority, or source authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificSourceCitationExact as Citation
import DASHI.Culture.MissingDeceasedScientistWorkAttributionExact as Atlas
import DASHI.Culture.MissingDeceasedScientificWorkCrossPollinationExact as Cross
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal

------------------------------------------------------------------------
-- Existing institutional/publication citation coverage.
------------------------------------------------------------------------

jplPrincipalDesignation2020 : Citation.ScientificCitation
jplPrincipalDesignation2020 =
  Citation.scientific-citation
    "NASA Jet Propulsion Laboratory"
    "JPL Principal Designation"
    "Jet Propulsion Laboratory Research"
    2020
    (Citation.canonicalURL "https://www.jpl.nasa.gov/site/research/research-community/awards-and-recognitions/jpl-principal/")
    "2020 table: Frank W. Maiwald - 389T Planetary Mass Spectrometry"
    Citation.institutionalRoleSource
    "Identifies Frank W. Maiwald as a JPL Principal in section 389T, Planetary Mass Spectrometry."

maiwaldPlanetaryMassCitation : Citation.AttributionWithCitation
maiwaldPlanetaryMassCitation =
  Citation.attribution-with-citation Atlas.maiwaldPlanetaryMassSpectrometry jplPrincipalDesignation2020

mitLoureiroProfile : Citation.ScientificCitation
mitLoureiroProfile =
  Citation.scientific-citation
    "Massachusetts Institute of Technology, Department of Physics"
    "Nuno F. G. Loureiro"
    "MIT Physics faculty profile"
    2026
    (Citation.canonicalURL "https://physics.mit.edu/faculty/nuno-gomes-loureiro/")
    "Research Interests: Magnetic Reconnection; Confinement and Transport in Fusion Plasmas"
    Citation.researchAreaSource
    "Documents Loureiro's magnetic-reconnection research, plasma turbulence, and confinement/transport work in fusion plasmas, and identifies Viriato as developed by Loureiro and colleagues."

loureiroReconnectionCitation : Citation.AttributionWithCitation
loureiroReconnectionCitation =
  Citation.attribution-with-citation Atlas.loureiroMagneticReconnection mitLoureiroProfile

loureiroFusionTransportCitation : Citation.AttributionWithCitation
loureiroFusionTransportCitation =
  Citation.attribution-with-citation Atlas.loureiroFusionConfinementTransport mitLoureiroProfile

ipacGrillmairStaffProfile : Citation.ScientificCitation
ipacGrillmairStaffProfile =
  Citation.scientific-citation
    "Caltech IPAC"
    "Carl Grillmair - Science Staff"
    "Infrared Processing and Analysis Center"
    2026
    (Citation.canonicalURL "https://www.ipac.caltech.edu/science/staff/carl")
    "Research Interests"
    Citation.researchAreaSource
    "Lists Grillmair's research interests including dark matter, Galactic structure, stellar populations, and exoplanets."

grillmairResearchCitation : Citation.AttributionWithCitation
grillmairResearchCitation =
  Citation.attribution-with-citation Atlas.grillmairStellarStreams ipacGrillmairStaffProfile

ipacGrillmairCV : Citation.ScientificCitation
ipacGrillmairCV =
  Citation.scientific-citation
    "Carl J. Grillmair"
    "Curriculum vitae / research grants"
    "Caltech IPAC staff site"
    2014
    (Citation.canonicalURL "https://web.ipac.caltech.edu/staff/carl/cgcv.html")
    "Research Grants: 2011 NASA Astrophysics Data Analysis proposal"
    Citation.projectRoleSource
    "Records the 2011 NASA Astrophysics Data Analysis proposal 'Stellar Debris Streams: Probing The Galactic Dark Matter Distribution with WISE and 2MASS' with PI Grillmair."

grillmairPICitation : Citation.AttributionWithCitation
ipacGrillmairPICitation =
  Citation.attribution-with-citation Atlas.grillmairStreamDistancePI ipacGrillmairCV

thomasVPS342014 : Citation.ScientificCitation
thomasVPS342014 =
  Citation.scientific-citation
    "William E. Dowdle; Beat Nyfeler; Jane Nagel; Robert A. Elling; Shanming Liu; Ellen Triantafellow; Suchithra Menon; Zuncai Wang; Ayako Honda; Gwynn Pardee; John Cantwell; Catherine Luu; Ivan Cornella-Taracido; Edmund Harrington; Peter Fekkes; Hong Lei; Qing Fang; Mary Ellen Digan; Debra Burdick; Andrew F. Powers; Stephen B. Helliwell; Simon D'Aquin; Julie Bastien; Henry Wang; Dmitri Wiederschain; Jenny Kuerth; Philip Bergman; David Schwalb; Jason Thomas; Savuth Ugwonali; Fred Harbinski; John Tallarico; Christopher J. Wilson; Vic E. Myer; Jeffery A. Porter; Dirksen E. Bussiere; Peter M. Finan; Mark A. Labow; Xiaohong Mao; Lawrence G. Hamann; Brendan D. Manning; Reginald A. Valdez; Thomas Nicholson; Markus Schirle; Mark S. Knapp; Erin P. Keaney; Leon O. Murphy"
    "Selective VPS34 inhibitor blocks autophagy and uncovers a role for NCOA4 in ferritin degradation and iron homeostasis in vivo"
    "Nature Cell Biology 16(11), 1069-1079"
    2014
    (Citation.doi "10.1038/ncb3053")
    "PMID 25327288"
    Citation.authorshipSource
    "Publication-level author list includes Jason Thomas; this is coauthorship, not sole project ownership."

thomasVPS34Citation : Citation.AttributionWithCitation
thomasVPS34Citation =
  Citation.attribution-with-citation Cross.jasonThomasVPS34 thomasVPS342014

------------------------------------------------------------------------
-- Exact DOI-bearing continuation / manifestation objects recovered by the
-- parallel snowball.  These are object citations, not proof of raw-data or
-- same-byte lineage across poster/preprint/SI/version-of-record manifestations.
------------------------------------------------------------------------

maiwaldProtonatedValine2024 : Citation.ScientificCitation
maiwaldProtonatedValine2024 =
  Citation.scientific-citation
    "Lane M. Terry; Maddie K. Klumb; Deacon J. Nemchick; Robert P. Hodyss; Frank W. Maiwald; J. Mathias Weber"
    "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
    "Journal of Physical Chemistry A"
    2024
    (Citation.doi "10.1021/acs.jpca.4c03552")
    "ACS article and Supporting Information; ChemRxiv DOI 10.26434/chemrxiv-2024-2tvc6"
    Citation.authorshipSource
    "Version-of-record authorship includes Frank Maiwald; Supporting Information is a public derivative product and does not by itself identify raw instrument-data custody or byte identity with the 2023 JPL poster."

maiwaldDeprotonatedStates2025 : Citation.ScientificCitation
maiwaldDeprotonatedStates2025 =
  Citation.scientific-citation
    "Lane M. Terry; Maddie K. Klumb; Deacon J. Nemchick; Robert P. Hodyss; J. Mathias Weber"
    "Probing Isomers and Conformers by Cryogenic Ion Vibrational Spectroscopy: Deprotonated States of Valine and Aminovaleric Acid"
    "Journal of Physical Chemistry A"
    2025
    (Citation.doi "10.1021/acs.jpca.5c03141")
    "ACS article and Supporting Information; ChemRxiv DOI 10.26434/chemrxiv-2025-xf3d2"
    Citation.authorshipSource
    "Version-of-record omits Maiwald while the 2023 JPL poster already displayed deprotonated experimental spectra; exact dataset, reduction, figure and contribution lineage remains a separate acquisition problem."

maiwaldISMS2024Deprotonated : Citation.ScientificCitation
maiwaldISMS2024Deprotonated =
  Citation.scientific-citation
    "Lane M. Terry; Deacon J. Nemchick; Robert Hodyss; Frank Maiwald; J. Mathias Weber"
    "Cryogenic Ion Vibrational Spectroscopy of Deprotonated Valine and Deprotonated Aminovaleric Acid"
    "77th International Symposium on Molecular Spectroscopy, University of Illinois Urbana-Champaign"
    2024
    (Citation.canonicalURL "https://isms.illinois.edu/2024/schedule/schedule_session.php?sID=1564")
    "P7658 / RL06; Thursday 2024-06-20, 15:15-15:30"
    Citation.authorshipSource
    "Official conference programme/abstract names Frank Maiwald as a JPL/Caltech coauthor and states that cryogenic gas-phase infrared spectra of deprotonated valine and deprotonated aminovaleric acid are presented. No DOI is invented for this conference object."

loureiroStudentContinuation2026 : Citation.ScientificCitation
loureiroStudentContinuation2026 =
  Citation.scientific-citation
    "Dion Li; Zhuo Liu; Nuno F. Loureiro"
    "Role of ion acoustic instability in magnetic reconnection"
    "Journal of Plasma Physics"
    2026
    (Citation.doi "10.1017/S002237782510113X")
    "Cambridge University Press article; published online 2026-02-27; MIT/PSFC publication listing"
    Citation.authorshipSource
    "Post-loss publication carrier involving Loureiro's named PhD student Dion Li. It supports scientific-output continuation, not formal advisor reassignment, grant succession, repository custody, or same-carrier handover."

------------------------------------------------------------------------
-- Snowball attribution/traversal binding.
------------------------------------------------------------------------

data SourceAuthorityClass : Set where
  primaryPeerReviewedPublication
  primaryInstitutionalRecord
  primaryGovernmentRecord
  primaryPatentRecord
  primaryConferenceRecord
  secondaryReportingLead : SourceAuthorityClass

record SnowballSourceCoordinate : Set where
  constructor snowball-source-coordinate
  field
    citation : Citation.ScientificCitation
    authorityClass : SourceAuthorityClass
    primaryEvidence : Bool
    coordinate : Traversal.DashiKnowledgeCoordinate
    qidVerified : Bool
    deweyCoordinateOnly : Bool
    qidCoordinateOnly : Bool
    boundedCoordinateReading : String

open SnowballSourceCoordinate public

loureiro2026SnowballCoordinate : SnowballSourceCoordinate
loureiro2026SnowballCoordinate = snowball-source-coordinate
  loureiroStudentContinuation2026
  primaryPeerReviewedPublication
  true
  (Traversal.dashi-knowledge-coordinate
    "DASHI/Culture/MissingDeceasedApplicationSuccessionFrontierExact.agda"
    "Nuno F. G. Loureiro student/publication continuation"
    "530 Physics"
    "Q51287446"
    "DOI 10.1017/S002237782510113X; ORCID 0000-0001-9755-6563")
  true true true
  "Q51287446 identifies Nuno F. G. Loureiro as an external semantic coordinate. Cambridge/MIT sources, not the QID or Dewey class, pay the publication/student-continuation claim."

maiwald2024SnowballCoordinate : SnowballSourceCoordinate
maiwald2024SnowballCoordinate = snowball-source-coordinate
  maiwaldProtonatedValine2024
  primaryPeerReviewedPublication
  true
  (Traversal.dashi-knowledge-coordinate
    "DASHI/Culture/MaiwaldActionSpectroscopyProjectSuccessionExact.agda"
    "Frank W. Maiwald action-spectroscopy publication lineage"
    "540 Chemistry"
    "unresolvedQid"
    "DOI 10.1021/acs.jpca.4c03552; JPL institution QID Q189325")
  false true true
  "No verified Frank Maiwald person-QID is owned here. Q189325 identifies JPL only and must not be promoted to a person identity."

maiwaldISMS2024SnowballCoordinate : SnowballSourceCoordinate
maiwaldISMS2024SnowballCoordinate = snowball-source-coordinate
  maiwaldISMS2024Deprotonated
  primaryConferenceRecord
  true
  (Traversal.dashi-knowledge-coordinate
    "DASHI/Culture/MaiwaldActionSpectroscopyProjectSuccessionExact.agda"
    "Frank W. Maiwald pre-loss deprotonated-spectra conference attribution"
    "540 Chemistry"
    "unresolvedQid"
    "ISMS P7658/RL06; 2024-06-20; JPL institution QID Q189325")
  false true true
  "Official conference object pays dated pre-loss presentation/authorship of the deprotonated spectra. It has no DOI and none is fabricated; unresolved person QID remains unresolved."

maiwald2025SnowballCoordinate : SnowballSourceCoordinate
maiwald2025SnowballCoordinate = snowball-source-coordinate
  maiwaldDeprotonatedStates2025
  primaryPeerReviewedPublication
  true
  (Traversal.dashi-knowledge-coordinate
    "DASHI/Culture/MaiwaldActionSpectroscopyProjectSuccessionExact.agda"
    "post-loss deprotonated action-spectroscopy publication lineage"
    "540 Chemistry"
    "unresolvedQid"
    "DOI 10.1021/acs.jpca.5c03141; JPL institution QID Q189325")
  false true true
  "Person QID remains unresolved. DOI identifies the publication object, not the 2023 poster bytes, raw spectra, or calibration-transfer state."

loureiroProfileSnowballCoordinate : SnowballSourceCoordinate
loureiroProfileSnowballCoordinate = snowball-source-coordinate
  mitLoureiroProfile
  primaryInstitutionalRecord
  true
  (Traversal.dashi-knowledge-coordinate
    "DASHI/Physics/Plasma/LoureiroViriatoPlasmoidBidiExact.agda"
    "Nuno F. G. Loureiro plasma-science attribution"
    "530 Physics"
    "Q51287446"
    "MIT Physics faculty profile; QID Q51287446; ORCID 0000-0001-9755-6563")
  true true true
  "MIT pays the institutional/research attribution. QID/ORCID are identity/search coordinates and do not transfer source authority."

jplMaiwaldInstitutionCoordinate : Traversal.DashiKnowledgeCoordinate
jplMaiwaldInstitutionCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Culture/MissingDeceasedScientificWorkSourceRegistryExtendedExact.agda"
  "Jet Propulsion Laboratory institutional coordinate for Maiwald sources"
  "620 Engineering"
  "Q189325"
  "NASA Jet Propulsion Laboratory institutional records"

------------------------------------------------------------------------
-- Boundary: DOI/QID/Dewey/primary-source roles remain non-interchangeable.
------------------------------------------------------------------------

record SnowballAttributionBoundary : Set where
  constructor snowball-attribution-boundary
  field
    doiAddedWhenVerified : Bool
    noDoiInventedForNonDoiObjects : Bool
    unresolvedQidNeverGuessed : Bool
    qidCoordinateDoesNotCreatePersonWeld : Bool
    institutionQidDoesNotCreatePersonQid : Bool
    deweyCoordinateDoesNotCreateAuthority : Bool
    doiDoesNotCreateSameByteIdentityAcrossVersions : Bool
    primarySourceClassDoesNotExpandBoundedClaim : Bool
    secondaryRepetitionDoesNotCreateIndependentCorroboration : Bool

open SnowballAttributionBoundary public

canonicalSnowballAttributionBoundary : SnowballAttributionBoundary
canonicalSnowballAttributionBoundary = snowball-attribution-boundary
  true true true true true true true true true

record ExtendedSourceCoverageBoundary : Set where
  constructor extended-source-coverage-boundary
  field
    institutionalProfilesUsedWhenNoDOIAppropriate : Bool
    institutionalProfilesUsedWhenNoDOIAppropriateIsTrue :
      institutionalProfilesUsedWhenNoDOIAppropriate ≡ true
    publicationDOIUsedWhenAvailable : Bool
    publicationDOIUsedWhenAvailableIsTrue :
      publicationDOIUsedWhenAvailable ≡ true
    PIClaimUsesRoleSpecificInstitutionalReceipt : Bool
    PIClaimUsesRoleSpecificInstitutionalReceiptIsTrue :
      PIClaimUsesRoleSpecificInstitutionalReceipt ≡ true
    traversalCoordinatesSeparatedFromEvidenceAuthority : Bool
    traversalCoordinatesSeparatedFromEvidenceAuthorityIsTrue :
      traversalCoordinatesSeparatedFromEvidenceAuthority ≡ true

canonicalExtendedSourceCoverageBoundary : ExtendedSourceCoverageBoundary
canonicalExtendedSourceCoverageBoundary =
  extended-source-coverage-boundary true refl true refl true refl true refl