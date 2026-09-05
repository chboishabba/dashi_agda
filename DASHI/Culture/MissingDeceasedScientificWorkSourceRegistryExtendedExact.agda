module DASHI.Culture.MissingDeceasedScientificWorkSourceRegistryExtendedExact where

------------------------------------------------------------------------
-- EXTENDED SOURCE COVERAGE
--
-- Completes citation bindings for scientific-work claims whose best source is
-- institutional rather than DOI-bearing, and adds publication-level metadata
-- where a DOI can be verified.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ScientificSourceCitationExact as Citation
import DASHI.Culture.MissingDeceasedScientistWorkAttributionExact as Atlas
import DASHI.Culture.MissingDeceasedScientificWorkCrossPollinationExact as Cross

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
grillmairPICitation =
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

canonicalExtendedSourceCoverageBoundary : ExtendedSourceCoverageBoundary
canonicalExtendedSourceCoverageBoundary =
  extended-source-coverage-boundary true refl true refl true refl
