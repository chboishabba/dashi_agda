module DASHI.Law.SensibLawWrongTypeGridCoverageCountermodelExact where

-- DASHI-original logical countermodel to unqualified nine-cell coverage.
--
-- SOURCE / ATTRIBUTION:
-- Rob McNamara, "A System of Wrong", Episode 4 ("The Grid"),
-- user-supplied transcript 2026-09-30: "every serious wrong ... sits in
-- one of these cells"; "No cell is empty". Neither assertion is a theorem.
-- McNamara attributes the broader philosophy to Forrest Landry; no
-- independent attribution of the precise nine-cell thesis is made.
--
-- Queensland Nature Conservation Act 1992, s 89, authorised compilation
-- current as at 16 June 2026 (checked 2026-09-30):
-- https://www.legislation.qld.gov.au/view/pdf/inforce/current/act-1992-020
-- Section 89 concerns restrictions on taking protected plants in the wild,
-- subject to its statutory qualifications, exceptions and defences.
-- It does NOT establish the absence of all possible philosophical frames.
--
-- The propositions proven here are CONDITIONAL on the explicitly given
-- semantic frame-basis predicates; they do not prove a real offence is
-- incapable of fitting under every conceivable broader interpretation.
-- The native WrongType record permits empty relationshipConstraintIds:
-- emptiness never by itself proves that a social relationship is absent.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Law.SensibLawWrongTypeCareTransactionPowerGridExact as Grid

-- A cell assignment is JUSTIFIED only when the frame violated and the
-- imposed frame BOTH have an evidential or semantic basis in context.
record Grounding (w : Ontology.WrongType) : Set₁ where
  field
    violatedBasis : Grid.Mode → Set
    imposedBasis  : Grid.Mode → Set

GroundedCell : (w : Ontology.WrongType) → Grounding w → Grid.Cell → Set
GroundedCell w grounding c =
  Grounding.violatedBasis grounding (Grid.Cell.violatedFrame c)
  × Grounding.imposedBasis grounding (Grid.Cell.imposedLogic c)

AllCellsExcluded : (w : Ontology.WrongType) → Grounding w → Set
AllCellsExcluded w g =
  (c : Grid.Cell) → GroundedCell w g c → ⊥

-- The empty violated-frame interpretation is an explicit consistent
-- extension of the ontology: no WrongType axiom forces Care, Transaction
-- or Power in the underlying record.
emptyViolated : (w : Ontology.WrongType) → Grounding w
emptyViolated w = record
  { violatedBasis = λ _ → ⊥
  ; imposedBasis = λ _ → ⊤ }

emptyViolatedExcludesAll : (w : Ontology.WrongType) →
  AllCellsExcluded w (emptyViolated w)
emptyViolatedExcludesAll w c grounded = proj₁ grounded

-- A concrete native WrongType with no required relationship constraints;
-- illustrative analytical fixture, NOT an asserted legal encoding of s 89.
ecosystemFixture : Ontology.WrongType
ecosystemFixture = Ontology.wrongTypeRecord
  (Ontology.stableId "fixture:non-relational-ecosystem")
  (Ontology.stableId "legal-system:QLD")
  ((Ontology.stableId "source:QLD:NatureConservationAct1992:s89") ∷ [])
  ((Ontology.stableId "interest:ecosystem") ∷ [])
  [] [] Ontology.strict [] [] []

ecosystemHasNoRequiredRelationship :
  Ontology.WrongType.relationshipConstraintIds ecosystemFixture ≡ []
ecosystemHasNoRequiredRelationship = refl

-- Under explicit no-grounding semantics it admits NO cell. In particular,
-- existing data types cannot prove universal grounded coverage.
ecosystemNoGroundedCell :
  AllCellsExcluded ecosystemFixture (emptyViolated ecosystemFixture)
ecosystemNoGroundedCell = emptyViolatedExcludesAll ecosystemFixture

-- No illicit conclusion that s 89 has no other possible interpretation.
-- Absence of a relationship requirement != proof relationships cannot exist.
