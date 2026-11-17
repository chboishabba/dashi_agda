module DASHI.Culture.AmyEskridgeVideoHistoricalPrimaryControlsExact where

-- Primary historical and experimental controls from direct source reading.
-- Sources retained with original investigators; DASHI only owns the
-- attribution/contradiction/next-receipt arrangement.
--
-- Podkletnov and Nieminen, "A possibility of gravitational force shielding
-- by bulk YBa2Cu3O7-x superconductor", Physica C 203 (1992) pp.441-444,
-- DOI 10.1016/0921-4534(92)90055-H.
-- Original full paper scanned:
-- https://robertfrancisjr.com/pdfs/A%20Possibility%20of%20Gravitational%20Force%20Shielding%20by%20Bulk%20Superconductor.pdf
--
-- U.S. General Accounting Office, B-167034, 1970-06-23,
-- "Implementation Of 1970 Defense Procurement Authorization Act Requiring
-- Relationship Of Research To Specific Military Functions":
-- https://www.gao.gov/products/b-167034
-- Source for Public Law 91-121 s203 of 1969, not a 1973 antigravity-specific
-- mandate. This establishes funding limits, not covert classification.
--
-- Nick Cook, "Anti-gravity propulsion comes 'out of the closet'",
-- Jane's Defence Weekly, 29 July 2002, source transcription:
-- https://archive.md/lG1GW
-- The reporting predates video assertion that Boeing first admitted GRASP
-- in 2014. This is *firsthand journalism*, not a Boeing-issued project
-- completion receipt and not proof that antigravity works.
--
-- NASA NTRS rotating-field report #19990019627 and Li et al. 1997 static
-- DOI 10.1016/S0921-4534(97)01462-7 are INSPECTED separately in
-- AmyEskridgeVideoPrimaryInspectionExact.
-- Do not use different apparatus as strict experimental refutations.

open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import DASHI.Core.Prelude using (⊥)
import DASHI.Culture.AmyEskridgeVideoClaimAttributionLedgerExact as Video

data PrimaryEvidenceKind : Set where
  originalExperimentalPaper : PrimaryEvidenceKind
  officialGovernmentAudit : PrimaryEvidenceKind
  contemporaneousInvestigation : PrimaryEvidenceKind

data ComparisonOutcome : Set where
  originalAuthorReports : ComparisonOutcome
  dateContradictsNarrator : ComparisonOutcome
  legalInferenceNotSupported : ComparisonOutcome

record HighAlphaHistoricalControl : Set where
  constructor historical-control
  field
    associatedVideoClaim : Video.RawAttributedClaim
    originalAttribution : String
    exactRecord : String
    originalDocumentURL : String
    kind : PrimaryEvidenceKind
    boundedReading : String
    comparison : ComparisonOutcome
    stillOpen : String

podkletnovOriginal1992 : HighAlphaHistoricalControl
podkletnovOriginal1992 = historical-control
  Video.claim043
  "E. Podkletnov; R. Nieminen; Physica C 203 (1992) 441-444; DOI 10.1016/0921-4534(92)90055-H"
  "Original 4-page paper, p.441 experimental setup and p.442 figure/results"
  "https://robertfrancisjr.com/pdfs/A%20Possibility%20of%20Gravitational%20Force%20Shielding%20by%20Bulk%20Superconductor.pdf"
  originalExperimentalPaper
  "145 mm diameter, 6 mm thick YBCO disk with liquid helium; 5.47834 g sample about 15 mm above levitating disk behind plastic foil; electro-optical balance; claimed 0.05 percent static and 0.3 percent stable rotating weight decrease; transient readings fluctuated from -2.5 to +5.4 percent"
  originalAuthorReports
  "Independent raw readings and controls for air/He currents, electrostatic effects, vibration, magnetic coupling, and replication of later 2 percent claim"

mansfieldGAO1970 : HighAlphaHistoricalControl
mansfieldGAO1970 = historical-control
  Video.claim049
  "U.S. General Accounting Office, B-167034, published 1970-06-23"
  "Implementation of 1970 Defense Procurement Authorization Act Requiring Relationship of Research to Specific Military Functions; Public Law 91-121 s203"
  "https://www.gao.gov/products/b-167034"
  officialGovernmentAudit
  "GAO identifies 1969 Public Law 91-121 section 203 limiting FY1970 Defense research funding to projects with direct and apparent relationship to a specific military function; no rule that antigravity must be classified"
  legalInferenceNotSupported
  "Find exact later amendment variations; demonstrate each actual project-funding decision rather than extrapolating a government-wide prohibition"

boeingJane2002 : HighAlphaHistoricalControl
boeingJane2002 = historical-control
  Video.claim053
  "Nick Cook, Jane's Defence Weekly, 29 July 2002"
  "Anti-gravity propulsion comes 'out of the closet'; reporting Boeing Phantom Works programme GRASP"
  "https://archive.md/lG1GW"
  contemporaneousInvestigation
  "Contemporaneous reporting described Boeing/Phantom Works interest and obtained GRASP briefing; 2002 precedes video's supposed first 2014 acknowledgement"
  dateContradictsNarrator
  "Obtain Boeing-authorized statement, original GRASP briefing, contract, outputs and engineering experiments to infer actual programme state"

historicalControls : List HighAlphaHistoricalControl
historicalControls = podkletnovOriginal1992 ∷ mansfieldGAO1970 ∷ boeingJane2002 ∷ []

-- No source-class promotion from a science paper to industry results,
-- a law governing budgets to secret classification, or investigative
-- reporting to successful apparatus development.
data LawRequiresSecretAntigravityResearch : Set where
data PatentOrMediaProvesAntigravityDevice : Set where

noMansfieldClassificationShortcut : LawRequiresSecretAntigravityResearch → ⊥
noMansfieldClassificationShortcut ()

noMediaApparatusShortcut : PatentOrMediaProvesAntigravityDevice → ⊥
noMediaApparatusShortcut ()
