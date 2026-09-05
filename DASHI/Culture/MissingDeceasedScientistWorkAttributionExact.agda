module DASHI.Culture.MissingDeceasedScientistWorkAttributionExact where

------------------------------------------------------------------------
-- MISSING / DECEASED SCIENTIST WORK ATTRIBUTION ATLAS
--
-- This module attaches named people to documented scientific or technical work
-- under DASHI's attribution policy.  It does NOT assert that the cases below
-- are causally connected, that anyone was targeted because of their work, or
-- that every person in the wider media roster was a scientist.
--
-- Attribution is role-exact:
--   inventor is used only where an inventor record names the person;
--   author is used only where a publication/report names the person;
--   PI/lead is used only where an institutional record names that role;
--   affiliation/leadership is not upgraded into authorship of subordinate work.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- Michael David Hicks
-- JPL Family News / AAS DPS obituary: JPL research scientist 1998-2022;
-- specialty physical properties of comets and asteroids; science teams DART,
-- NEAT, Dawn, and Deep Space 1; >80 peer-reviewed papers.
------------------------------------------------------------------------

hicksCometAsteroidResearch : Attribution.ScientificWorkAttribution
hicksCometAsteroidResearch =
  Attribution.scientific-work-attribution
    "Michael David Hicks"
    "physical properties of comets and asteroids"
    "NASA Jet Propulsion Laboratory"
    Attribution.institutionalResearchRole
    Attribution.primaryInstitutionalRecord
    "JPL Family News, October 2023; AAS Division for Planetary Sciences memorial, Michael David Hicks (1964-2023)"
    "Institutional/disciplinary sources identify this as Hicks's research specialty."
    Attribution.externalSourceOwner

hicksDARTTeam : Attribution.ScientificWorkAttribution
hicksDARTTeam =
  Attribution.scientific-work-attribution
    "Michael David Hicks"
    "DART Project science team"
    "NASA Double Asteroid Redirection Test"
    Attribution.namedTeamMember
    Attribution.primaryInstitutionalRecord
    "JPL Family News, October 2023; AAS DPS memorial"
    "Source names Hicks as a member of the DART science team; this does not make him sole author or owner of DART."
    Attribution.externalSourceOwner

hicksNEATTeam : Attribution.ScientificWorkAttribution
hicksNEATTeam =
  Attribution.scientific-work-attribution
    "Michael David Hicks"
    "Near Earth Asteroid Tracking science team"
    "NASA/JPL NEAT"
    Attribution.namedTeamMember
    Attribution.primaryInstitutionalRecord
    "JPL Family News, October 2023; AAS DPS memorial"
    "Source names Hicks as a science-team member."
    Attribution.externalSourceOwner

hicksDawnTeam : Attribution.ScientificWorkAttribution
hicksDawnTeam =
  Attribution.scientific-work-attribution
    "Michael David Hicks"
    "Dawn Mission science team"
    "NASA Dawn"
    Attribution.namedTeamMember
    Attribution.primaryInstitutionalRecord
    "JPL Family News, October 2023; AAS DPS memorial"
    "Source names Hicks as a science-team member."
    Attribution.externalSourceOwner

hicksDeepSpace1Team : Attribution.ScientificWorkAttribution
hicksDeepSpace1Team =
  Attribution.scientific-work-attribution
    "Michael David Hicks"
    "Deep Space 1 science team"
    "NASA Deep Space 1"
    Attribution.namedTeamMember
    Attribution.primaryInstitutionalRecord
    "JPL Family News, October 2023; AAS DPS memorial"
    "Source names Hicks as a science-team member."
    Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Frank W. Maiwald
-- JPL Principal Designation identifies section 389T Planetary Mass
-- Spectrometry. JPL SURP 2023 names Maiwald as PI of the biosignature project.
------------------------------------------------------------------------

maiwaldPlanetaryMassSpectrometry : Attribution.ScientificWorkAttribution
maiwaldPlanetaryMassSpectrometry =
  Attribution.scientific-work-attribution
    "Frank W. Maiwald"
    "planetary mass spectrometry"
    "NASA Jet Propulsion Laboratory, section 389T"
    Attribution.institutionalResearchRole
    Attribution.primaryInstitutionalRecord
    "JPL Principal Designation, 2020"
    "JPL's institutional principal registry places Maiwald in Planetary Mass Spectrometry."
    Attribution.externalSourceOwner

maiwaldBiosignaturePI : Attribution.ScientificWorkAttribution
maiwaldBiosignaturePI =
  Attribution.scientific-work-attribution
    "Frank W. Maiwald"
    "Unambiguous Detection of Biosignatures by Action Spectroscopy"
    "JPL Strategic University Research Partnerships, 2023"
    Attribution.namedPrincipalInvestigator
    Attribution.primaryInstitutionalRecord
    "JPL SURP 2023 project registry"
    "The JPL project registry explicitly names Frank W. Maiwald as PI; collaborators remain separately attributed."
    Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Monica Jacinto Reza / Monica Jacinto
-- The patent record supplies the strongest role-exact attribution: inventor.
-- The House Oversight letter separately records a JPL Materials Processing
-- Group directorship but explicitly derives the surrounding relationship claim
-- from public reporting, so the two source strengths are not collapsed.
------------------------------------------------------------------------

rezaBurnResistantAlloyPatent : Attribution.ScientificWorkAttribution
rezaBurnResistantAlloyPatent =
  Attribution.scientific-work-attribution
    "Monica Jacinto (later Monica Reza)"
    "Burn-resistant and high tensile strength metal alloys"
    "Rockwell/Boeing/Rocketdyne patent lineage"
    Attribution.namedInventor
    Attribution.primaryPatentRecord
    "US20040208777A1 / US10/769,195; priority 2001-09-18; inventors Monica Jacinto and Dallis Hardwick"
    "Patent record names Monica Jacinto and Dallis Hardwick as inventors; DASHI does not convert inventorship into sole ownership or into claims about later applications."
    Attribution.externalSourceOwner

rezaMaterialsProcessingDirector : Attribution.ScientificWorkAttribution
rezaMaterialsProcessingDirector =
  Attribution.scientific-work-attribution
    "Monica Reza"
    "Materials Processing Group leadership"
    "NASA Jet Propulsion Laboratory"
    Attribution.institutionalLeadershipRole
    Attribution.officialDocumentRepeatingPublicReporting
    "U.S. House Committee on Oversight and Government Reform letter to DOE, 20 April 2026, page 1"
    "The congressional letter states that Reza served as director of JPL's Materials Processing Group, but its footnote lineage is public reporting; this is not promoted to a primary JPL personnel receipt here."
    Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Joshua Kyle LeBlanc
-- NASA NTRS 20250008475 both names him as an author and identifies him in the
-- FICS Executive Committee as NASA Space Nuclear Propulsion I&C TechMat lead.
------------------------------------------------------------------------

leblancFissionSurfacePowerAuthor : Attribution.ScientificWorkAttribution
leblancFissionSurfacePowerAuthor =
  Attribution.scientific-work-attribution
    "Joshua Leblanc"
    "NASA 40 kW Fission Surface Power I and C Technology Development Path"
    "NASA Fission Surface Power / Space Nuclear Propulsion instrumentation and controls"
    Attribution.namedAuthor
    Attribution.primaryInstitutionalRecord
    "NASA Technical Reports Server, document 20250008475"
    "NASA NTRS names Joshua Leblanc of Marshall Space Flight Center in the author list."
    Attribution.externalSourceOwner

leblancSnpICLead : Attribution.ScientificWorkAttribution
leblancSnpICLead =
  Attribution.scientific-work-attribution
    "Joshua Leblanc"
    "Space Nuclear Propulsion instrumentation-and-controls technology maturation"
    "NASA Fission Instrumentation and Controls executive committee"
    Attribution.namedTechnicalLead
    Attribution.primaryInstitutionalRecord
    "NASA NTRS 20250008475, FICS Executive Committee recognition slide"
    "NASA source explicitly labels Leblanc 'NASA SNP I&C TechMat Team Lead'."
    Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Nuno F. G. Loureiro
-- MIT owns the institutional biography; the scientific works remain Loureiro's
-- and his coauthors' under their publication-level attribution.
------------------------------------------------------------------------

loureiroMagneticReconnection : Attribution.ScientificWorkAttribution
loureiroMagneticReconnection =
  Attribution.scientific-work-attribution
    "Nuno F. G. Loureiro"
    "magnetic reconnection theory and simulation"
    "MIT Plasma Science and Fusion Center / MIT Physics"
    Attribution.institutionalResearchRole
    Attribution.primaryInstitutionalRecord
    "MIT Physics faculty memorial/profile; MIT PSFC profile"
    "MIT identifies magnetic reconnection as a central Loureiro research area."
    Attribution.externalSourceOwner

loureiroFusionConfinementTransport : Attribution.ScientificWorkAttribution
loureiroFusionConfinementTransport =
  Attribution.scientific-work-attribution
    "Nuno F. G. Loureiro"
    "confinement and transport in fusion plasmas"
    "MIT Plasma Science and Fusion Center"
    Attribution.institutionalResearchRole
    Attribution.primaryInstitutionalRecord
    "MIT Physics faculty memorial/profile"
    "MIT identifies turbulence, macroscopic instabilities, confinement and transport as Loureiro research areas."
    Attribution.externalSourceOwner

loureiroViriato : Attribution.ScientificWorkAttribution
loureiroViriato =
  Attribution.scientific-work-attribution
    "Nuno F. G. Loureiro and colleagues"
    "Viriato reduced-gyrokinetics simulation code"
    "plasma turbulence / reduced gyrokinetics"
    Attribution.namedAuthor
    Attribution.primaryPublicationRecord
    "N. F. Loureiro et al., Computer Physics Communications 206, 45-63 (2016), as identified by MIT Physics"
    "MIT states that Viriato was developed by Loureiro and colleagues; coauthorship is preserved rather than collapsed into sole authorship."
    Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Carl J. Grillmair
------------------------------------------------------------------------

grillmairStellarStreams : Attribution.ScientificWorkAttribution
grillmairStellarStreams =
  Attribution.scientific-work-attribution
    "Carl J. Grillmair"
    "stellar streams, Galactic structure, and dark-matter probing"
    "Caltech IPAC"
    Attribution.institutionalResearchRole
    Attribution.primaryInstitutionalRecord
    "Caltech IPAC Science Staff profile and 2026 memorial"
    "IPAC identifies Grillmair's research in Galactic structure, stellar populations, dark matter and stellar streams."
    Attribution.externalSourceOwner

grillmairCrossroadsAuthor : Attribution.ScientificWorkAttribution
grillmairCrossroadsAuthor =
  Attribution.scientific-work-attribution
    "Carl J. Grillmair"
    "At a Crossroads: Stellar Streams in the South Galactic Cap"
    "Astrophysical Journal 847(2), 119 (2017)"
    Attribution.namedAuthor
    Attribution.primaryPublicationRecord
    "DOI 10.3847/1538-4357/aa8872; CaltechAUTHORS record"
    "CaltechAUTHORS names Grillmair as creator/author; the paper reports four cold stellar-stream candidates."
    Attribution.externalSourceOwner

grillmairStreamDistancePI : Attribution.ScientificWorkAttribution
grillmairStreamDistancePI =
  Attribution.scientific-work-attribution
    "Carl J. Grillmair"
    "stellar debris streams / Galactic dark-matter distribution with WISE and 2MASS"
    "NASA Astrophysics Data Analysis"
    Attribution.namedPrincipalInvestigator
    Attribution.primaryInstitutionalRecord
    "Carl Grillmair IPAC CV; 2011 NASA Astrophysics Data Analysis proposal"
    "Institutional CV explicitly records Grillmair as PI."
    Attribution.externalSourceOwner

------------------------------------------------------------------------
-- William Neil McCasland
-- Technical leadership is kept distinct from authorship of every AFRL project.
------------------------------------------------------------------------

mccaslandAFRLLeadership : Attribution.ScientificWorkAttribution
mccaslandAFRLLeadership =
  Attribution.scientific-work-attribution
    "William N. McCasland"
    "management of the Air Force science and technology programme"
    "Air Force Research Laboratory"
    Attribution.institutionalLeadershipRole
    Attribution.primaryInstitutionalRecord
    "U.S. Air Force official biography, Major General William N. McCasland, current as of April 2013"
    "Official biography states that as AFRL commander he managed the Air Force science and technology programme and customer-funded R&D; this does not make him author/inventor of every AFRL project."
    Attribution.externalSourceOwner

mccaslandSpaceVehiclesLeadership : Attribution.ScientificWorkAttribution
mccaslandSpaceVehiclesLeadership =
  Attribution.scientific-work-attribution
    "William N. McCasland"
    "Space Vehicles Directorate / Phillips Research Site leadership"
    "Air Force Research Laboratory, Kirtland AFB"
    Attribution.institutionalLeadershipRole
    Attribution.primaryInstitutionalRecord
    "U.S. Air Force official biography; AFRL official history"
    "Official biography records Materiel Wing Director, AFRL Space Vehicles Directorate, and Commander, Phillips Research Site, 2001-2004."
    Attribution.externalSourceOwner

mccaslandPayloadAndSpaceAcquisition : Attribution.ScientificWorkAttribution
mccaslandPayloadAndSpaceAcquisition =
  Attribution.scientific-work-attribution
    "William N. McCasland"
    "payload development, GPS chief engineering, space-based laser programme direction, and space acquisition"
    "United States Air Force / National Reconnaissance Office-associated career assignments"
    Attribution.institutionalResearchRole
    Attribution.primaryInstitutionalRecord
    "U.S. Air Force official biography"
    "The official biography enumerates these engineering/acquisition assignments; the record is role attribution, not authorship of every technical artifact from those programmes."
    Attribution.externalSourceOwner

------------------------------------------------------------------------
-- The reported Reza-McCasland relationship remains deliberately weaker than
-- either person's independently documented technical work.
------------------------------------------------------------------------

rezaMcCaslandReportedRelationship : Attribution.PersonRelationshipAttribution
rezaMcCaslandReportedRelationship =
  Attribution.person-relationship-attribution
    "Monica Reza"
    "William Neil McCasland"
    "reported close professional connection through an Air Force-funded early-2000s advanced-materials programme"
    Attribution.officialDocumentRepeatingPublicReporting
    "House Oversight letter to DOE, 20 April 2026, page 1, lines corresponding to the cited public-report allegation"
    "Congress records that public reports alleged this connection; the letter does not independently establish the relationship, so DASHI does not promote it to primary technical evidence."

------------------------------------------------------------------------
-- Roster boundary.
------------------------------------------------------------------------

record NamedScientificWorkRosterBoundary : Set where
  constructor named-scientific-work-roster-boundary
  field
    namesAttachedOnlyAtSupportedRole : Bool
    namesAttachedOnlyAtSupportedRoleIsTrue :
      namesAttachedOnlyAtSupportedRole ≡ true

    causalConnectionBetweenCasesAsserted : Bool
    causalConnectionBetweenCasesAssertedIsFalse :
      causalConnectionBetweenCasesAsserted ≡ false

    sensitiveWorkImpliesCauseOfDeathOrDisappearance : Bool
    sensitiveWorkImpliesCauseOfDeathOrDisappearanceIsFalse :
      sensitiveWorkImpliesCauseOfDeathOrDisappearance ≡ false

    sameEmployerImpliesSameProject : Bool
    sameEmployerImpliesSameProjectIsFalse :
      sameEmployerImpliesSameProject ≡ false

    leadershipImpliesAuthorshipOfSubordinateResearch : Bool
    leadershipImpliesAuthorshipOfSubordinateResearchIsFalse :
      leadershipImpliesAuthorshipOfSubordinateResearch ≡ false

    pressReportedRelationshipUpgradedByCongressionalRepetition : Bool
    pressReportedRelationshipUpgradedByCongressionalRepetitionIsFalse :
      pressReportedRelationshipUpgradedByCongressionalRepetition ≡ false

canonicalNamedScientificWorkRosterBoundary : NamedScientificWorkRosterBoundary
canonicalNamedScientificWorkRosterBoundary =
  named-scientific-work-roster-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
