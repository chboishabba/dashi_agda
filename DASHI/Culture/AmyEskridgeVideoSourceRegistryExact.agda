module DASHI.Culture.AmyEskridgeVideoSourceRegistryExact where

-- DASHI source registry for the 17 November 2026 user-supplied
-- "She Researched Something THEY DON'T ALLOW. Then She Died" transcript.
-- See Docs/SourceAttributionPolicy.md.
-- Original primary source != speaker report != external verification.
--
-- Original institutional source, date and article:
-- House Oversight & Government Reform, "Comer & Burlison Seek Information
-- on Missing Nuclear and Rocket Scientists", 2026-04-20,
-- https://oversight.house.gov/release/comer-burlison-seek-information-on-missing-nuclear-and-rocket-scientists/
-- Original agency correspondence, FBI copy, 2026-04-20:
-- https://oversight.house.gov/wp-content/uploads/2026/04/FBI-Missing-Scientists-Letter_4.20.26.pdf
-- Inspection: House article and FBI letter page 1 in source audit.
-- The House calls the media reports UNCONFIRMED and specifies AT LEAST TEN.
--
-- US 1,655,144 (1928), *Grain-treating machine*, inventors
-- Joseph Hallgarth and Earl E. Chandler:
-- https://patents.google.com/patent/US1655144A/en
-- US 1,655,114 (1928), *Apparatus for aerial transportation*,
-- inventor Nikola Tesla:
-- https://patents.google.com/patent/US1655114A/en
-- Inspection: patent landing-page inventor/title/abstract/specification.
--
-- Daryl J. Bem, "Feeling the Future: Experimental Evidence for Anomalous
-- Retroactive Influences on Cognition and Affect", JPSP 100(3), 407-425
-- (2011), DOI 10.1037/a0021524, PMID 21280961.
-- https://pubmed.ncbi.nlm.nih.gov/21280961/
-- Inspection: NLM bibliographic identity and abstract only.
--
-- These bounded checks DO NOT independently verify propulsion, surveillance,
-- precognition, or an intelligence operation.

open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Bool using (Bool; true; false)

data SourceClass : Set where
  institutionalPrimary : SourceClass
  patentPrimary : SourceClass
  scholarlyBibliographic : SourceClass
  firstPersonInterview : SourceClass
  secondaryReport : SourceClass
  unresolvedLead : SourceClass

data InspectedExtent : Set where
  metadataAndNamedPassage : InspectedExtent
  abstractOnly : InspectedExtent
  reporterAccountOnly : InspectedExtent
  notInspected : InspectedExtent

record ScopedSource : Set where
  constructor scoped-source
  field
    attribution : String
    title : String
    locator : String
    sourceClass : SourceClass
    inspection : InspectedExtent
    sourcePays : String
    sourceDoesNotPay : String

open ScopedSource public

houseApril2026 : ScopedSource
houseApril2026 = scoped-source
  "House Oversight and Government Reform; Comer and Burlison"
  "Comer & Burlison Seek Information on Missing Nuclear and Rocket Scientists; FBI letter 2026-04-20"
  "https://oversight.house.gov/wp-content/uploads/2026/04/FBI-Missing-Scientists-Letter_4.20.26.pdf"
  institutionalPrimary metadataAndNamedPassage
  "The committee requested a briefing and described unconfirmed media reports alleging at least ten deaths/disappearances beginning in 2023"
  "A verified eleven-person roster, actual shared programme, wrongdoing or operational targeting"

hallgarthChandlerPatent : ScopedSource
hallgarthChandlerPatent = scoped-source
  "Joseph Hallgarth; Earl E. Chandler"
  "Grain-treating machine"
  "US1655144A; https://patents.google.com/patent/US1655144A/en"
  patentPrimary metadataAndNamedPassage
  "The patent number used for Tesla in the video is assigned to a grain-treating invention by other inventors"
  "The video's alleged Tesla space drive"

teslaAerialPatent : ScopedSource
teslaAerialPatent = scoped-source
  "Nikola Tesla"
  "Apparatus for aerial transportation"
  "US1655114A; https://patents.google.com/patent/US1655114A/en"
  patentPrimary metadataAndNamedPassage
  "A Tesla aircraft patent describing propeller-based thrust for vertical/horizontal flight"
  "Proof of a space-drive, antigravity shielding, or vacuum reactionless propulsion"

bem2011 : ScopedSource
bem2011 = scoped-source
  "Daryl J. Bem"
  "Feeling the Future: Experimental Evidence for Anomalous Retroactive Influences on Cognition and Affect"
  "DOI 10.1037/a0021524; PMID 21280961; https://pubmed.ncbi.nlm.nih.gov/21280961/"
  scholarlyBibliographic abstractOnly
  "Bem published nine experiments claiming retroactive influences on cognition/affect"
  "Independent replication, anticipatory-physiology clip identity, alternate timelines or future-viewing machine"

burischCamelot : ScopedSource
burischCamelot = scoped-source
  "Dan Burisch; Project Camelot, interview conducted by Kerry Cassidy and Bill Ryan"
  "Stargate Secrets, June 2007"
  "https://projectcamelot.org/dan_burisch.html"
  firstPersonInterview reporterAccountOnly
  "A primary speaker-level recording for Burisch's own claims and the clip-source family"
  "Independent confirmation of Majestic 12 employment, Looking Glass, Stargates, secret custody or time travel"

videoTranscript : ScopedSource
videoTranscript = scoped-source
  "Unidentified video narrator and quoted clips"
  "She Researched Something THEY DON'T ALLOW. Then She Died"
  "User-provided 32:44 timestamped transcript; video URL and upload date not supplied"
  unresolvedLead notInspected
  "That the submitted transcript contains narrator statements and quotations at given timestamps"
  "Correct clip identification, original footage integrity, primary scientific validation or an actual eleven-person roster"

-- Thomas Townsend Brown, Electrokinetic apparatus, US 2,949,550,
-- filed 1957, granted 1960:
-- https://patents.google.com/patent/US2949550A/en
-- Henry William Wallace, Method and apparatus for generating a
-- secondary gravitational force field, US 3,626,605:
-- https://patents.google.com/patent/US3626605A/en
--
brown1960 : ScopedSource
brown1960 = scoped-source
  "Thomas Townsend Brown"
  "Electrokinetic apparatus"
  "US2949550A; https://patents.google.com/patent/US2949550A/en"
  patentPrimary metadataAndNamedPassage
  "A high-voltage electrode patent describes relative movement through a surrounding dielectric medium"
  "A validated vacuum antigravity effect or reactionless thrust"

wallace1971 : ScopedSource
wallace1971 = scoped-source
  "Henry William Wallace"
  "Method and apparatus for generating a secondary gravitational force field"
  "US3626605A; https://patents.google.com/patent/US3626605A/en"
  patentPrimary metadataAndNamedPassage
  "A granted patent claims a kinemassic rotating nuclear-spin field"
  "Independent reproducibility or measured gravity modification"

sourceRegistry : List ScopedSource
sourceRegistry = houseApril2026 ∷ hallgarthChandlerPatent ∷
  teslaAerialPatent ∷ brown1960 ∷ wallace1971 ∷
  bem2011 ∷ burischCamelot ∷ videoTranscript ∷ []

-- Representation gates: an asserted source class is not a proof of its content.
data SourceMetadataProvesCausalTargeting : Set where
data InterviewRecordingProvesDeviceExists : Set where
data NumberOfCitationsProvesIndependence : Set where
