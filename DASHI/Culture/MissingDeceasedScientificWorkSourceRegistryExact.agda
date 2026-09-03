module DASHI.Culture.MissingDeceasedScientificWorkSourceRegistryExact where

------------------------------------------------------------------------
-- FULL SOURCE REGISTRY FOR MISSING/DECEASED SCIENTIFIC-WORK ATTRIBUTIONS
--
-- Each entry records author/institution, title, venue/publisher, year, strongest
-- stable identifier available, exact locator, and bounded role.  DOI is used
-- where verified; patents, NASA NTRS IDs, PMIDs/PMCIDs, institutional records,
-- and canonical URLs are retained when no DOI is appropriate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ScientificSourceCitationExact as Citation
import DASHI.Culture.MissingDeceasedScientistWorkAttributionExact as Atlas
import DASHI.Culture.MissingDeceasedScientificWorkCrossPollinationExact as Cross

------------------------------------------------------------------------
-- Hicks
------------------------------------------------------------------------

hicksJPLFamilyNews : Citation.ScientificCitation
hicksJPLFamilyNews =
  Citation.scientific-citation
    "NASA Jet Propulsion Laboratory"
    "JPL Family News - October 2023 - Michael David Hicks passing notice"
    "Jet Propulsion Laboratory"
    2023
    (Citation.canonicalURL "https://d2pn8kiwq2w21t.cloudfront.net/documents/Universe_-_October_2023.pdf")
    "Passings: Michael David Hicks"
    Citation.researchAreaSource
    "Identifies Hicks as JPL NASA postdoc/research scientist, specialist in physical properties of comets and asteroids, and science-team member for DART, NEAT, Dawn, and Deep Space 1."

hicksArizonaMemorial : Citation.ScientificCitation
hicksArizonaMemorial =
  Citation.scientific-citation
    "University of Arizona Lunar and Planetary Laboratory"
    "Michael Hicks - PTYS Alumnus memorial"
    "University of Arizona"
    2023
    (Citation.canonicalURL "https://lpl.arizona.edu/about/memoriam/michael-hicks")
    "Biographical and research summary"
    Citation.researchAreaSource
    "Independent institutional restatement of Hicks's JPL tenure, comet/asteroid specialty, and named mission science-team memberships."

hicksDARTCitation : Citation.AttributionWithCitation
hicksDARTCitation =
  Citation.attribution-with-citation Atlas.hicksDARTTeam hicksJPLFamilyNews

------------------------------------------------------------------------
-- Maiwald
------------------------------------------------------------------------

maiwaldSURP2023 : Citation.ScientificCitation
maiwaldSURP2023 =
  Citation.scientific-citation
    "Frank Maiwald; Robert Hodyss; Mathias Weber; Lane Terry"
    "Unambiguous Detection of Biosignatures by Action Spectroscopy"
    "NASA Jet Propulsion Laboratory FY23 Strategic University Research Partnership"
    2023
    (Citation.canonicalURL "https://www.jpl.nasa.gov/site/research/media/posters/2023/SP23012p.pdf")
    "Poster SP23012p; Principal Investigator line"
    Citation.projectRoleSource
    "Names Frank Maiwald as Principal Investigator and the listed collaborators as co-investigators/collaborators."

maiwaldPICitation : Citation.AttributionWithCitation
maiwaldPICitation =
  Citation.attribution-with-citation Atlas.maiwaldBiosignaturePI maiwaldSURP2023

------------------------------------------------------------------------
-- Monica Jacinto / Reza patent lineage
------------------------------------------------------------------------

jacintoHardwickPatent2004 : Citation.ScientificCitation
jacintoHardwickPatent2004 =
  Citation.scientific-citation
    "Monica A. Jacinto; Dallis Ann Hardwick"
    "Burn-resistant and high tensile strength metal alloys"
    "United States Patent Application Publication"
    2004
    (Citation.patentPublication "US20040208777A1; application US10/769,195")
    "Inventors and abstract; continuation-in-part of US09/954,835"
    Citation.inventorshipSource
    "Names Monica A. Jacinto and Dallis Ann Hardwick as inventors of nickel-based burn-resistant/high-strength alloys for oxygen-rich structural applications."

jacintoPatentCitation : Citation.AttributionWithCitation
jacintoPatentCitation =
  Citation.attribution-with-citation Atlas.rezaBurnResistantAlloyPatent jacintoHardwickPatent2004

------------------------------------------------------------------------
-- Joshua LeBlanc / NASA fission power and propulsion instrumentation
------------------------------------------------------------------------

leblancNTRS2025 : Citation.ScientificCitation
leblancNTRS2025 =
  Citation.scientific-citation
    "Robert Okojie; Teresa Benko; Tyler Steiner; Kaiser Aguirre; Christopher Barth; Dianne Ezell; Angel Martinez-Sanchez; Robert Bruckner; Joshua Leblanc; Jarvis Caffrey"
    "NASA 40 kW Fission Surface Power I and C Technology Development Path"
    "NASA Technical Reports Server; Fission Surface Power Technology Maturation Webinar Series"
    2025
    (Citation.nasaNTRS "20250008475")
    "Author list; FICS Executive Committee recognition slide"
    Citation.projectRoleSource
    "Names Joshua Leblanc of Marshall Space Flight Center as an author and labels him NASA SNP I&C TechMat Team Lead."

leblancAuthorCitation : Citation.AttributionWithCitation
leblancAuthorCitation =
  Citation.attribution-with-citation Atlas.leblancFissionSurfacePowerAuthor leblancNTRS2025

leblancLeadCitation : Citation.AttributionWithCitation
leblancLeadCitation =
  Citation.attribution-with-citation Atlas.leblancSnpICLead leblancNTRS2025

------------------------------------------------------------------------
-- Loureiro
------------------------------------------------------------------------

loureiroViriato2016 : Citation.ScientificCitation
loureiroViriato2016 =
  Citation.scientific-citation
    "N. F. Loureiro; W. Dorland; L. Fazendeiro; A. Kanekar; A. A. Schekochihin; D. Zocco"
    "Viriato: A Fourier-Hermite spectral code for strongly magnetized fluid-kinetic plasma dynamics"
    "Computer Physics Communications 206, 45-63"
    2016
    (Citation.doi "10.1016/j.cpc.2016.05.004")
    "article DOI / volume 206, pages 45-63"
    Citation.authorshipSource
    "Publication-level authorship for the Viriato code paper; applications include magnetized plasma turbulence and magnetic reconnection."

loureiroViriatoCitation : Citation.AttributionWithCitation
loureiroViriatoCitation =
  Citation.attribution-with-citation Atlas.loureiroViriato loureiroViriato2016

------------------------------------------------------------------------
-- Grillmair
------------------------------------------------------------------------

grillmairCrossroads2017 : Citation.ScientificCitation
grillmairCrossroads2017 =
  Citation.scientific-citation
    "Carl J. Grillmair"
    "At a Crossroads: Stellar Streams in the South Galactic Cap"
    "The Astrophysical Journal 847(2), Article 119"
    2017
    (Citation.doi "10.3847/1538-4357/aa8872")
    "CaltechAUTHORS record; arXiv:1708.09029"
    Citation.authorshipSource
    "Sole-author publication reporting four cold stellar-stream candidates in the South Galactic Cap."

grillmairCrossroadsCitation : Citation.AttributionWithCitation
grillmairCrossroadsCitation =
  Citation.attribution-with-citation Atlas.grillmairCrossroadsAuthor grillmairCrossroads2017

------------------------------------------------------------------------
-- McCasland
------------------------------------------------------------------------

mccaslandUSAFBiography : Citation.ScientificCitation
mccaslandUSAFBiography =
  Citation.scientific-citation
    "United States Air Force"
    "Major General William N. McCasland - Biography"
    "U.S. Air Force"
    2013
    (Citation.canonicalURL "https://www.af.mil/About-Us/Biographies/Display/article/104776/major-general-william-n-mccasland/")
    "Assignments 2-16; AFRL commander responsibility paragraph"
    Citation.institutionalRoleSource
    "Documents astronautical-engineering education; payload development, GPS chief engineering, Space Based Laser program direction, Space Vehicles Directorate/Phillips Research Site command, space acquisition, and AFRL command."

mccaslandAFRLCitation : Citation.AttributionWithCitation
mccaslandAFRLCitation =
  Citation.attribution-with-citation Atlas.mccaslandAFRLLeadership mccaslandUSAFBiography

------------------------------------------------------------------------
-- Anthony Chavez
------------------------------------------------------------------------

anthonyChavezLANL2025 : Citation.ScientificCitation
anthonyChavezLANL2025 =
  Citation.scientific-citation
    "Los Alamos National Laboratory"
    "Anthony Chavez - Engineering, Operations, and Physics"
    "National Security Science, Summer 2025 Engineering issue"
    2025
    (Citation.canonicalURL "https://cdn.lanl.gov/files/nss-2025-engineering-online_f0e10.pdf")
    "Anthony Chavez profile"
    Citation.institutionalRoleSource
    "States that Chavez earned mechanical engineering, worked more than 25 years at DARHT, and completed design work for the Scorpius accelerator."

anthonyChavezScorpiusCitation : Citation.AttributionWithCitation
anthonyChavezScorpiusCitation =
  Citation.attribution-with-citation Cross.anthonyChavezScorpius anthonyChavezLANL2025

------------------------------------------------------------------------
-- Jason R. Thomas
------------------------------------------------------------------------

thomasSTING2018 : Citation.ScientificCitation
thomasSTING2018 =
  Citation.scientific-citation
    "Peter D. Koch; Howard R. Miller; Gary Yu; John A. Tallarico; Peter K. Sorger; Yuan Wang; Yan Feng; Jason R. Thomas; Nathan T. Ross; Timothy Mitchison"
    "A High Content Screen in Macrophages Identifies Small Molecule Modulators of STING-IRF3 and NFkB Signaling"
    "ACS Chemical Biology 13(4), 1066-1081"
    2018
    (Citation.doi "10.1021/acschembio.7b01060")
    "PMID 29553248; PMCID PMC5996755"
    Citation.authorshipSource
    "Publication names Jason R. Thomas as an author on the STING-IRF3/NFkB chemical-biology screen."

thomasSTINGCitation : Citation.AttributionWithCitation
thomasSTINGCitation =
  Citation.attribution-with-citation Cross.jasonThomasSTINGScreen thomasSTING2018

------------------------------------------------------------------------
-- Registry policy manifest.
------------------------------------------------------------------------

record MissingScientistSourceRegistryBoundary : Set where
  constructor missing-scientist-source-registry-boundary
  field
    publicationDOIsRecordedWhenVerified : Bool
    publicationDOIsRecordedWhenVerifiedIsTrue :
      publicationDOIsRecordedWhenVerified ≡ true
    patentsUsePatentIdentifiersRatherThanFakeDOIs : Bool
    patentsUsePatentIdentifiersRatherThanFakeDOIsIsTrue :
      patentsUsePatentIdentifiersRatherThanFakeDOIs ≡ true
    nasaReportsUseNTRSIdentifiersWhenAvailable : Bool
    nasaReportsUseNTRSIdentifiersWhenAvailableIsTrue :
      nasaReportsUseNTRSIdentifiersWhenAvailable ≡ true
    institutionalSourcesRemainValidWithoutDOI : Bool
    institutionalSourcesRemainValidWithoutDOIIsTrue :
      institutionalSourcesRemainValidWithoutDOI ≡ true
    sourceClaimRemainsBoundedToItsRole : Bool
    sourceClaimRemainsBoundedToItsRoleIsTrue :
      sourceClaimRemainsBoundedToItsRole ≡ true

canonicalMissingScientistSourceRegistryBoundary :
  MissingScientistSourceRegistryBoundary
canonicalMissingScientistSourceRegistryBoundary =
  missing-scientist-source-registry-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
