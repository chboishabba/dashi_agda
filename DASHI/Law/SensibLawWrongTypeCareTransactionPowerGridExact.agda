module DASHI.Law.SensibLawWrongTypeCareTransactionPowerGridExact where

-- DASHI-original relational INDEX over candidate wrongful conduct.
-- Attribution:
--   The Care/Transaction/Power 3 x 3 diagram is visible in the
--   uvsmpub / Rob McNamara "A System of Wrong" screenshot supplied
--   2026-09-29; its directional semantics and cell offence placements
--   are NOT verified as Forrest Landry's or McNamara's assertions.
--   The interpretation, predicates, and proofs below are DASHI work.
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
    actorMode : Mode
    contextMode : Mode

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
  "A System of Wrong (screenshot)" "user-supplied screenshot"
  "Care / Transaction / Power headings" "2026-09-29 supplied"

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
  (cell power transaction) "example:context-2"
  "example:evidence-pending" (queenslandCode "s 408C")
  "DASHI hypothetical classification; not a legal finding"

exampleManyCells : List GridCandidate
exampleManyCells = exampleCandidate₁ ∷ exampleCandidate₂ ∷ []

firstCellFits : Fits exampleId (cell transaction transaction) exampleManyCells
firstCellFits = inj₁ (refl , refl)

secondCellFits : Fits exampleId (cell power transaction) exampleManyCells
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
    (cell power care) "ss 245-246" ∷
  crimeCandidate "wrong:QLD:sexual-assault" sexualAssault
    (cell power power) "s 352" ∷
  crimeCandidate "wrong:QLD:murder" murder
    (cell power power) "s 302" ∷
  crimeCandidate "wrong:QLD:manslaughter" manslaughter
    (cell care power) "s 303" ∷
  crimeCandidate "wrong:QLD:stealing" theft
    (cell transaction transaction) "s 391" ∷
  crimeCandidate "wrong:QLD:fraud" fraud
    (cell transaction transaction) "s 408C" ∷
  crimeCandidate "wrong:QLD:robbery" robbery
    (cell power transaction) "s 409" ∷
  crimeCandidate "wrong:QLD:extortion" extortion
    (cell power transaction) "s 415" ∷
  crimeCandidate "wrong:QLD:kidnapping-ransom" kidnapping
    (cell power power) "s 354A" ∷
  crimeCandidate "wrong:QLD:burglary" burglary
    (cell power transaction) "s 419" ∷
  crimeCandidate "wrong:QLD:computer-misuse" cyberMisuse
    (cell transaction power) "s 408E" ∷
  []

-- A simple uninhabited evidence-free promotion remains impossible:
-- no ViolationReceipt or authority data is constructed anywhere here.
