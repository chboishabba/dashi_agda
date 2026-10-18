module DASHI.Law.SensibLawWrongTypeCareTransactionPowerGridExact where

-- DASHI-original relational INDEX over candidate wrongful conduct.
-- Attribution:
--   Rob McNamara's user-provided Episode 4 transcript (A System of
--   Wrong: The Grid) explicitly defines the FIRST axis as the frame
--   violated and the SECOND as the logic imposed. It assigns examples
--   to all nine cells and claims universality. Transcript provenance is
--   user-supplied; no official episode transcript URL or timestamp is known.
--   Attribution to Forrest Landry is McNamara's statement, not independently
--   verified authorship of this nine-cell classification.
--   Formal representations, implementations and proofs are DASHI work.
--   Neither universality nor criminality is established by this transcript.
--   Queensland Criminal Code Act 1899, ss 245-246, 354A, 391,
--   408C, 409, 415: primary-law locator identifiers for candidate
--   offence families only. The scheme never proves their elements.
--   Official statutory source (2024-08-09 historical version):
--   https://www.legislation.qld.gov.au/view/whole/html/inforce/2024-08-09/act-1899-009
--   Source identity != authority receipt != element payment != liability.
--   A contextual classification is neither an accusation nor a verdict.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology

data Mode : Set where
  care transaction power : Mode

record Cell : Set where
  constructor cell
  field
    violatedFrame : Mode
    imposedLogic : Mode

-- Not a closed or exhaustive classification of criminal law.
data Pattern : Set where
  neglect professionalNegligence fiduciaryAbuse : Pattern
  theft fraud extortion robbery assault kidnapping : Pattern
  murder manslaughter sexualAssault burglary : Pattern
  bribery publicPowerMisuse cyberMisuse environmentalHarm : Pattern

-- All records explicitly retain the same existing WrongType identity.
-- Candidate edges do not manufacture WrongType, LegalSource, or receipts.
record SourceLocator : Set where
  constructor sourceLocator
  field
    originator : String
    work : String
    canonicalURL : String
    pinpoint : String
    version : String

record GridCandidate : Set where
  constructor gridCandidate
  field
    wrongTypeId : Ontology.StableId
    pattern : Pattern
    relation : Cell
    circumstanceRef : String
    evidenceRef : String
    source : SourceLocator
    attributionScope : String

-- Attributions describe distinct origins, without implying equality.
videoDiagram : SourceLocator
videoDiagram = sourceLocator "Rob McNamara / uvsmpub"
  "A System of Wrong, Episode 4: The Grid (user-provided transcript)"
  "user-supplied transcript; no canonical episode URL supplied"
  "nine cell enumerations, after 'Three frames applied to three frames'"
  "2026-09-30 transcript supplied"

queenslandCode : String → SourceLocator
queenslandCode section = sourceLocator "Queensland Parliament"
  "Criminal Code Act 1899 (Qld)"
  "https://www.legislation.qld.gov.au/view/whole/html/inforce/2024-08-09/act-1899-009"
  section "2024-08-09 historical consolidation"

-- Classification is relational and may assign different cells to the
-- same WrongType occurrence; no exclusivity or cell completeness axiom.
Fits : Ontology.StableId → Cell → List GridCandidate → Set
Fits wrong coordinate [] = ⊥
Fits wrong coordinate (candidate ∷ rest) =
  ((GridCandidate.wrongTypeId candidate ≡ wrong)
   × (GridCandidate.relation candidate ≡ coordinate))
  ⊎ Fits wrong coordinate rest

-- A source-free structural demonstration, not an empirical allegation:
-- the same stable id can occur in two different cells.
exampleId : Ontology.StableId
exampleId = Ontology.stableId "example:abstract-wrong-type"

exampleCandidate₁ : GridCandidate
exampleCandidate₁ = gridCandidate exampleId fraud
  (cell transaction transaction) "example:context-1"
  "example:evidence-pending" (queenslandCode "s 408C")
  "DASHI hypothetical classification; not a legal finding"

exampleCandidate₂ : GridCandidate
exampleCandidate₂ = gridCandidate exampleId fraud
  (cell transaction power) "example:context-2"
  "example:evidence-pending" (queenslandCode "s 408C")
  "DASHI hypothetical classification; not a legal finding"

exampleManyCells : List GridCandidate
exampleManyCells = exampleCandidate₁ ∷ exampleCandidate₂ ∷ []

firstCellFits : Fits exampleId (cell transaction transaction) exampleManyCells
firstCellFits = inj₁ (refl , refl)

secondCellFits : Fits exampleId (cell transaction power) exampleManyCells
secondCellFits = inj₂ (inj₁ (refl , refl))

-- Defining an independent contextual test is deliberate: pattern labelling
-- is insufficient for the source-conditioned WrongElements of a WrongType.
record LegalAssessmentBoundary : Set₁ where
  field
    candidate : GridCandidate
    applicableNormEvidence : Set
    satisfiedElementEvidence : Set
    defenceAndExceptionReview : Set
    -- No function from GridCandidate alone to any liability receipt.

------------------------------------------------------------------------
-- OFFENCE FAMILIES: candidate relational indexing, not legal conclusions.
-- The source establishes the named offence family/locator, not our cell.
-- Empty event/evidence references must be filled before case evaluation.
------------------------------------------------------------------------

crimeCandidate : String → Pattern → Cell → String → GridCandidate
crimeCandidate identifier family coordinate section =
  gridCandidate (Ontology.stableId identifier) family coordinate
    "illustrative:context-not-established" "evidence:not-provided"
    (queenslandCode section) "DASHI illustrative cell; not attributed to statute or video"

illustrativeCrimes : List GridCandidate
illustrativeCrimes =
  crimeCandidate "wrong:QLD:assault" assault
    (cell care power) "ss 245-246" ∷
  crimeCandidate "wrong:QLD:sexual-assault" sexualAssault
    (cell care power) "s 352" ∷
  crimeCandidate "wrong:QLD:murder" murder
    (cell care power) "s 302" ∷
  crimeCandidate "wrong:QLD:manslaughter" manslaughter
    (cell care power) "s 303" ∷
  crimeCandidate "wrong:QLD:stealing" theft
    (cell transaction transaction) "s 391" ∷
  crimeCandidate "wrong:QLD:fraud" fraud
    (cell transaction transaction) "s 408C" ∷
  crimeCandidate "wrong:QLD:robbery" robbery
    (cell transaction power) "s 409" ∷
  crimeCandidate "wrong:QLD:extortion" extortion
    (cell transaction power) "s 415" ∷
  crimeCandidate "wrong:QLD:kidnapping-ransom" kidnapping
    (cell care power) "s 354A" ∷
  crimeCandidate "wrong:QLD:burglary" burglary
    (cell transaction power) "s 419" ∷
  crimeCandidate "wrong:QLD:computer-misuse" cyberMisuse
    (cell transaction power) "s 408E" ∷
  []

-- A simple uninhabited evidence-free promotion remains impossible:
-- no ViolationReceipt or authority data is constructed anywhere here.

------------------------------------------------------------------------
-- EPISODE 4 SOURCE-CLAIMS (NOT AN OFFENCE ELEMENTS OR LIABILITY TABLE).
-- The transcript is attributed to McNamara, who attributes his overall
-- framework to Landry. Authorship of each cell is not independently
-- verified against Landry's writing. Claims of exhaustive coverage,
-- historical universality, and relative severity remain unproved.
------------------------------------------------------------------------

record EpisodeCellClaim : Set where
  constructor episode-cell-claim
  field
    gridCell : Cell
    sourceLabel : String
    examplesAsSpoken : String
    transcriptProvenance : SourceLocator
    researchStatus : String

spoken : Mode → Mode → String → String → EpisodeCellClaim
spoken target imposed label examples =
  episode-cell-claim (cell target imposed) label examples videoDiagram
    "attributed speech; no independent legal verification"

episodeCells : List EpisodeCellClaim
episodeCells =
  spoken care care "care betrayed from within"
    "caregiver neglect; parent abandonment; self-serving institutions" ∷
  spoken care transaction "priced person"
    "trafficking; commodified intimacy; dating-app engagement metrics" ∷
  spoken care power "body safety life seized by force"
    "murder; assault; rape; enslavement" ∷
  spoken transaction care "rigged gift"
    "charity that obligates; aid with hidden strings" ∷
  spoken transaction transaction "corrupted ledger"
    "theft; fraud; forgery; embezzlement" ∷
  spoken transaction power "manufactured sale"
    "robbery; extortion; ransomware; protection racket; payday lender; nonnegotiable terms" ∷
  spoken power care "authority dissolved by sentiment"
    "judge rules for a friend; commander spares the guilty" ∷
  spoken power transaction "sold decision"
    "bribery; corruption; regulatory capture" ∷
  spoken power power "betrayal from within"
    "treason; sedition; insider subversion" ∷
  []

-- Each cell has a transcript-level witness (not a legal validity proof).
firstEpisodeCell : EpisodeCellClaim
firstEpisodeCell = spoken care care "care betrayed from within"
  "caregiver neglect; parent abandonment; self-serving institutions"

-- Source-attributed thesis, left as an empirical/legal research target:
-- "every serious wrong ... sits in one of these cells"; "no cell is empty".
-- These are NOT Agda postulates and are NOT exported as theorems.
