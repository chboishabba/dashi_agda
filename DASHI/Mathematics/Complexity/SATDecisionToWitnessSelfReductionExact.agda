module DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact where

------------------------------------------------------------------------
-- DECISION -> SEARCH BY BINARY SELF-REDUCTION
--
-- This is the exact algorithmic core used by SAT self-reducibility:
-- at each remaining Boolean variable, query one restricted branch; if that
-- branch is satisfiable take it, otherwise the split theorem forces the other
-- branch.  Hence an n-variable search uses exactly n decision queries.
--
-- This module deliberately separates the generic self-reduction theorem from
-- the BooleanFormula-specific substitution/variable-bound instantiation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)

record BinarySelfReduction : Set₁ where
  field
    Node : Nat → Set
    SatisfiableAt : ∀ {remaining} → Node remaining → Set
    Witness : Node zero → Set

    chooseFalse : ∀ {remaining} → Node (suc remaining) → Node remaining
    chooseTrue : ∀ {remaining} → Node (suc remaining) → Node remaining

    satisfiableSplits :
      ∀ {remaining} (node : Node (suc remaining)) →
      SatisfiableAt node →
      SatisfiableAt (chooseFalse node) ⊎
      SatisfiableAt (chooseTrue node)

    terminalWitness :
      (node : Node zero) →
      SatisfiableAt node →
      Witness node

open BinarySelfReduction public

record ExactDecisionOracle
    (reduction : BinarySelfReduction) : Set₁ where
  field
    decide :
      ∀ {remaining} →
      Node reduction remaining → Bool
    sound :
      ∀ {remaining} (node : Node reduction remaining) →
      decide node ≡ true →
      SatisfiableAt reduction node
    complete :
      ∀ {remaining} (node : Node reduction remaining) →
      SatisfiableAt reduction node →
      decide node ≡ true

open ExactDecisionOracle public

falseDecisionExcludesSatisfiable :
  ∀ {reduction : BinarySelfReduction}
    (oracle : ExactDecisionOracle reduction)
    {remaining}
    (node : Node reduction remaining) →
  decide oracle node ≡ false →
  SatisfiableAt reduction node →
  ⊥
falseDecisionExcludesSatisfiable oracle node decidedFalse satisfiable
    with complete oracle node satisfiable
... | ()

record SearchResult
    (reduction : BinarySelfReduction)
    (remaining : Nat)
    (start : Node reduction remaining) : Set₁ where
  field
    terminal : Node reduction zero
    witness : Witness reduction terminal
    decisionQueries : Nat
    exactQueryCount : decisionQueries ≡ remaining

open SearchResult public

recoverWitness :
  ∀ (reduction : BinarySelfReduction)
    (oracle : ExactDecisionOracle reduction)
    {remaining}
    (node : Node reduction remaining) →
  SatisfiableAt reduction node →
  SearchResult reduction remaining node
recoverWitness reduction oracle {zero} node satisfiable = record
  { terminal = node
  ; witness = terminalWitness reduction node satisfiable
  ; decisionQueries = zero
  ; exactQueryCount = refl
  }
recoverWitness reduction oracle {suc remaining} node satisfiable
    with decide oracle (chooseFalse reduction node)
... | true =
  let nextSat =
        sound oracle
          (chooseFalse reduction node)
          refl
      recursive =
        recoverWitness reduction oracle
          (chooseFalse reduction node)
          nextSat
  in record
      { terminal = terminal recursive
      ; witness = witness recursive
      ; decisionQueries = suc (decisionQueries recursive)
      ; exactQueryCount =
          cong-suc (exactQueryCount recursive)
      }
  where
    cong-suc : ∀ {left right} → left ≡ right → suc left ≡ suc right
    cong-suc refl = refl
... | false with satisfiableSplits reduction node satisfiable
... | inj₁ falseSat =
  contradiction
    (falseDecisionExcludesSatisfiable
      oracle
      (chooseFalse reduction node)
      refl
      falseSat)
  where
    contradiction : ⊥ → SearchResult reduction (suc remaining) node
    contradiction ()
... | inj₂ trueSat =
  let recursive =
        recoverWitness reduction oracle
          (chooseTrue reduction node)
          trueSat
  in record
      { terminal = terminal recursive
      ; witness = witness recursive
      ; decisionQueries = suc (decisionQueries recursive)
      ; exactQueryCount =
          cong-suc (exactQueryCount recursive)
      }
  where
    cong-suc : ∀ {left right} → left ≡ right → suc left ≡ suc right
    cong-suc refl = refl

record SATDecisionSearchBoundary : Set where
  constructor sat-decision-search-boundary
  field
    binarySelfReductionRecoveryConstructed : Bool
    exactOneDecisionQueryPerVariable : Bool
    polynomialQueryCountForPolynomialVariableBound : Bool
    booleanFormulaSubstitutionInstantiationConstructed : Bool
    pEqualsNPDerived : Bool

canonicalSATDecisionSearchBoundary : SATDecisionSearchBoundary
canonicalSATDecisionSearchBoundary =
  sat-decision-search-boundary
    true true true false false
