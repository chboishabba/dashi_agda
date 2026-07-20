module DASHI.Philosophy.ClosureKinds where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Stage-nine closure is indexed by grammar and by closure kind.

data ClosureKind : Set where
  epistemicClosure : ClosureKind
  practicalClosure : ClosureKind
  relationalClosure : ClosureKind
  politicalClosure : ClosureKind
  administrativeClosure : ClosureKind

record IndexedClosure (State Grammar Witness : Set) : Set₁ where
  field
    state : State
    grammar : Grammar
    kind : ClosureKind
    witness : Witness
    provisional : Bool
    finalMetaphysicalClosureClaimed : Bool

open IndexedClosure public

record ClosureProfile (State Grammar Witness : Set) : Set₁ where
  field
    epistemic : IndexedClosure State Grammar Witness
    practical : IndexedClosure State Grammar Witness
    relational : IndexedClosure State Grammar Witness
    political : IndexedClosure State Grammar Witness
    kindsNeedNotCoincide : Set

open ClosureProfile public

record ClosureBoundary : Set where
  constructor mkClosureBoundary
  field
    practicalImpliesEpistemic : Bool
    administrativeImpliesCausalUnderstanding : Bool
    stageNineIsFinalTruth : Bool
    closureMustNameGrammar : Bool

open ClosureBoundary public

canonicalClosureBoundary : ClosureBoundary
canonicalClosureBoundary =
  mkClosureBoundary false false false true

canonicalStageNineNotFinal :
  stageNineIsFinalTruth canonicalClosureBoundary ≡ false
canonicalStageNineNotFinal = refl
