module DASHI.Ontology.LeanWikidataConstraintBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge
import DASHI.Cognition.PNF.WikidataRepairProposal as Repair

------------------------------------------------------------------------
-- The property/constraint side of James's development covers executable
-- property closure, single/distinct value constraints, statement constraints,
-- P1963 profiles, entity schemas, path evaluation and a mereology/class-order
-- separation.  These become typed diagnostic evidence in DASHI.  Failure of a
-- checker is not itself a negative world fact; explicit source theorems such as
-- `part_not_subclass` are separately represented as negative constraints.
------------------------------------------------------------------------

data LeanConstraintKind : Set where
  propertyConstraint statementConstraint typePropertyConstraint schemaConstraint : LeanConstraintKind
  pathConstraint mereologyNoClassConfusion : LeanConstraintKind

record LeanConstraintWitness : Set where
  constructor leanConstraintWitness
  field
    constraintKind : LeanConstraintKind
    theoremContract : LeanTheoremContract
    sourceMatched : Bool
    theoremAccepted : Bool
    sourceReferences : List String

open LeanConstraintWitness public

constraintWitnessState : LeanConstraintWitness → EpistemicTrit
constraintWitnessState witness =
  theoremReceiptState (theoremAccepted witness) (sourceMatched witness)

p1963CompletenessContract : LeanTheoremContract
p1963CompletenessContract = contract18

schemaConformanceContract : LeanTheoremContract
schemaConformanceContract = contract19

partNotSubclassContract : LeanTheoremContract
partNotSubclassContract = contract35

partNotInstanceContract : LeanTheoremContract
partNotInstanceContract = contract36

-- Review-only: a constraint witness can motivate a repair proposal, but the
-- existing repair boundary forbids it from asserting ontology truth or editing.
constraintRepairBoundary : Repair.WikidataRepairBoundary
constraintRepairBoundary = Repair.canonicalWikidataRepairBoundary

constraintCarriesEditAuthority : LeanConstraintWitness → Bool
constraintCarriesEditAuthority _ = false

constraintCarriesEditAuthorityFalse :
  (witness : LeanConstraintWitness) → constraintCarriesEditAuthority witness ≡ false
constraintCarriesEditAuthorityFalse witness = refl

checkerFailureUnresolved :
  (witness : LeanConstraintWitness) →
  theoremAccepted witness ≡ false →
  constraintWitnessState witness ≡ unresolved
checkerFailureUnresolved witness refl with sourceMatched witness
... | false = refl
... | true = refl
