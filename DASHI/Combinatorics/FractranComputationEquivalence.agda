module DASHI.Combinatorics.FractranComputationEquivalence where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Combinatorics.FractranCOL using (EV5; step; run)

------------------------------------------------------------------------
-- FRACTRAN computation equivalence boundary.
--
-- This module separates three claims that are easy to conflate:
--
--   1. two inputs have the same terminal result;
--   2. a source machine is faithfully represented by FRACTRAN states;
--   3. every arbitrary program admits such a representation.
--
-- (1) is a relation.  (2) requires an explicit bridge witness.  (3) is
-- not derived here and remains a non-promotion boundary.
------------------------------------------------------------------------

SameOutcome : EV5 → EV5 → Set
SameOutcome x y = run x ≡ run y

sameOutcome-refl : ∀ x → SameOutcome x x
sameOutcome-refl x = refl

sameOutcome-sym : ∀ {x y} → SameOutcome x y → SameOutcome y x
sameOutcome-sym = sym

sameOutcome-trans :
  ∀ {x y z} → SameOutcome x y → SameOutcome y z → SameOutcome x z
sameOutcome-trans = trans

------------------------------------------------------------------------
-- A source computation and a witness that one source step is represented
-- by the FRACTRAN transition surface.
------------------------------------------------------------------------

record SourceMachine : Set₁ where
  field
    State : Set
    sourceStep : State → Maybe State
    sourceRun  : State → State

open SourceMachine public

record FractranRepresentation (M : SourceMachine) : Set₁ where
  field
    encode : State M → EV5

    preserves-halt :
      ∀ {s} →
      sourceStep M s ≡ nothing →
      step (encode s) ≡ nothing

    preserves-step :
      ∀ {s s'} →
      sourceStep M s ≡ just s' →
      step (encode s) ≡ just (encode s')

    preserves-run :
      ∀ s →
      encode (sourceRun M s) ≡ run (encode s)

open FractranRepresentation public

sourceSameOutcome :
  (M : SourceMachine) →
  State M →
  State M →
  Set
sourceSameOutcome M x y = sourceRun M x ≡ sourceRun M y

representation-preserves-same-outcome :
  ∀ {M} →
  (R : FractranRepresentation M) →
  {x y : State M} →
  sourceSameOutcome M x y →
  SameOutcome (encode R x) (encode R y)
representation-preserves-same-outcome R {x} {y} same =
  trans
    (sym (preserves-run R x))
    (trans (cong (encode R) same) (preserves-run R y))

------------------------------------------------------------------------
-- Canonical catalogue: many encoded states may be assigned one key, but
-- the catalogue must prove that replacing an entry by its representative
-- preserves the terminal FRACTRAN result.
------------------------------------------------------------------------

record FractranCatalogue : Set₁ where
  field
    Key : Set
    key : EV5 → Key
    representative : Key → EV5

    representative-sound :
      ∀ x → SameOutcome (representative (key x)) x

    key-complete-for-outcome :
      ∀ {x y} → key x ≡ key y → SameOutcome x y

open FractranCatalogue public

catalogue-roundtrip :
  (C : FractranCatalogue) →
  ∀ x → run (representative C (key C x)) ≡ run x
catalogue-roundtrip C = representative-sound C

------------------------------------------------------------------------
-- Honest scope boundary.
------------------------------------------------------------------------

data FractranUniversalityStatus : Set where
  concreteMachineAndConditionalRepresentationOnly :
    FractranUniversalityStatus

record FractranUniversalityBoundary : Set where
  field
    status : FractranUniversalityStatus

    concreteFractranMachinePresent : Bool
    arbitraryProgramCompilerDerivedHere : Bool
    arbitraryProgramCompilerDerivedHereIsFalse :
      arbitraryProgramCompilerDerivedHere ≡ false

    catalogueCompressionDerivedWithoutWitness : Bool
    catalogueCompressionDerivedWithoutWitnessIsFalse :
      catalogueCompressionDerivedWithoutWitness ≡ false

    notes : List String

open FractranUniversalityBoundary public

canonicalFractranUniversalityBoundary : FractranUniversalityBoundary
canonicalFractranUniversalityBoundary =
  record
    { status = concreteMachineAndConditionalRepresentationOnly
    ; concreteFractranMachinePresent = true
    ; arbitraryProgramCompilerDerivedHere = false
    ; arbitraryProgramCompilerDerivedHereIsFalse = refl
    ; catalogueCompressionDerivedWithoutWitness = false
    ; catalogueCompressionDerivedWithoutWitnessIsFalse = refl
    ; notes =
        "Same terminal outcome is weaker than identical implementation or trace"
        ∷ "A source-to-FRACTRAN reduction must provide halt, step, and run preservation witnesses"
        ∷ "A canonical catalogue must prove representative soundness and key completeness"
        ∷ "No universal compiler, Monster-group classifier, token mechanism, or 71-fold theorem is promoted here"
        ∷ []
    }
