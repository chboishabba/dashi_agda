module DASHI.Mathematics.Complexity.PNotEqualsNPSATShannonSemanticAuthorityExact where

------------------------------------------------------------------------
-- SAT-SPECIFIC NON-CIRCULAR SEMANTIC LAW: SHANNON CONSISTENCY
--
-- For an EXACT SAT decision oracle D and any formula with a head variable:
--
--   D(phi) = D(phi[x:=false]) OR D(phi[x:=true]).
--
-- This is not an encoding trick and does not compute D(phi) first.  It follows
-- directly from SAT semantics:
--
--   SAT(phi) iff SAT(phi|false) or SAT(phi|true).
--
-- Therefore this is a genuine P11-style semantic authority forced by being a
-- correct SAT decider.
--
-- The second half of the owner measures the limitation: recursively expanding
-- this identity over all variables yields a complete binary authority tree.
-- The semantic law is real; naive iteration of it is exponential.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search

------------------------------------------------------------------------
-- Exact one-step Shannon law for every correct SAT oracle.
------------------------------------------------------------------------

satDecisionShannon :
  (oracle : SAT.SATDecisionOracle) →
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula (suc variables)) →
  Search.decide oracle formula
  ≡
  SAT.orBool
    (Search.decide oracle
      (SAT.restrictHead false formula))
    (Search.decide oracle
      (SAT.restrictHead true formula))
satDecisionShannon oracle formula
    with Search.decide oracle formula
       | Search.decide oracle (SAT.restrictHead false formula)
       | Search.decide oracle (SAT.restrictHead true formula)
... | true | true | right =
  refl
... | true | false | true =
  refl
... | true | false | false
    with Search.sound oracle formula refl
...   | parentSat
    with SAT.satisfiableSplits formula parentSat
...     | inj₁ falseSat
      with Search.complete
        oracle
        (SAT.restrictHead false formula)
        falseSat
...       | ()
...     | inj₂ trueSat
      with Search.complete
        oracle
        (SAT.restrictHead true formula)
        trueSat
...       | ()
... | false | false | false =
  refl
... | false | true | right =
  ⊥-elim
    (falseParentButFalseBranchSat right)
  where
    falseParentButFalseBranchSat :
      Bool →
      ⊥
    falseParentButFalseBranchSat rightValue
      with Search.sound
        oracle
        (SAT.restrictHead false formula)
        refl
...   | falseBranchSat
      with Search.complete
        oracle
        formula
        (SAT.liftFalse formula falseBranchSat)
...     | ()
... | false | false | true =
  ⊥-elim falseParentButTrueBranchSat
  where
    falseParentButTrueBranchSat : ⊥
    falseParentButTrueBranchSat
      with Search.sound
        oracle
        (SAT.restrictHead true formula)
        refl
...   | trueBranchSat
      with Search.complete
        oracle
        formula
        (SAT.liftTrue formula trueBranchSat)
...     | ()

------------------------------------------------------------------------
-- Binary semantic-authority tree induced by repeated Shannon expansion.
------------------------------------------------------------------------

data ShannonAuthorityTree : Nat → Set where
  shannonLeaf :
    Bool →
    ShannonAuthorityTree zero

  shannonBranch :
    ∀ {depth : Nat} →
    ShannonAuthorityTree depth →
    ShannonAuthorityTree depth →
    ShannonAuthorityTree (suc depth)

shannonTreeLeafCount :
  ∀ {depth : Nat} →
  ShannonAuthorityTree depth →
  Nat
shannonTreeLeafCount (shannonLeaf value) =
  suc zero
shannonTreeLeafCount (shannonBranch left right) =
  shannonTreeLeafCount left
  +
  shannonTreeLeafCount right

shannonTreeNodeCount :
  ∀ {depth : Nat} →
  ShannonAuthorityTree depth →
  Nat
shannonTreeNodeCount (shannonLeaf value) =
  suc zero
shannonTreeNodeCount (shannonBranch left right) =
  suc
    (shannonTreeNodeCount left
     +
     shannonTreeNodeCount right)

pow2 : Nat → Nat
pow2 zero =
  suc zero
pow2 (suc depth) =
  pow2 depth + pow2 depth

------------------------------------------------------------------------
-- Build the full decision tree by recursively restricting all variables.
------------------------------------------------------------------------

fullShannonAuthority :
  (oracle : SAT.SATDecisionOracle) →
  ∀ {variables : Nat} →
  SAT.BooleanFormula variables →
  ShannonAuthorityTree variables
fullShannonAuthority oracle {zero} formula =
  shannonLeaf (Search.decide oracle formula)
fullShannonAuthority oracle {suc variables} formula =
  shannonBranch
    (fullShannonAuthority
      oracle
      (SAT.restrictHead false formula))
    (fullShannonAuthority
      oracle
      (SAT.restrictHead true formula))

shannonTreeValue :
  ∀ {depth : Nat} →
  ShannonAuthorityTree depth →
  Bool
shannonTreeValue (shannonLeaf value) =
  value
shannonTreeValue (shannonBranch left right) =
  SAT.orBool
    (shannonTreeValue left)
    (shannonTreeValue right)

fullShannonAuthorityLeafCount :
  (oracle : SAT.SATDecisionOracle) →
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables) →
  shannonTreeLeafCount
    (fullShannonAuthority oracle formula)
  ≡ pow2 variables
fullShannonAuthorityLeafCount oracle {zero} formula =
  refl
fullShannonAuthorityLeafCount
    oracle {suc variables} formula
    rewrite
      fullShannonAuthorityLeafCount
        oracle
        (SAT.restrictHead false formula)
      |
      fullShannonAuthorityLeafCount
        oracle
        (SAT.restrictHead true formula) =
  refl

fullShannonAuthorityComputesRootDecision :
  (oracle : SAT.SATDecisionOracle) →
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables) →
  shannonTreeValue
    (fullShannonAuthority oracle formula)
  ≡
  Search.decide oracle formula
fullShannonAuthorityComputesRootDecision
    oracle {zero} formula =
  refl
fullShannonAuthorityComputesRootDecision
    oracle {suc variables} formula =
  transitive
    (congruence
      (fullShannonAuthorityComputesRootDecision
        oracle
        (SAT.restrictHead false formula))
      (fullShannonAuthorityComputesRootDecision
        oracle
        (SAT.restrictHead true formula)))
    (symmetry
      (satDecisionShannon oracle formula))
  where
    congruence :
      ∀ {left₁ left₂ right₁ right₂ : Bool} →
      left₁ ≡ left₂ →
      right₁ ≡ right₂ →
      SAT.orBool left₁ right₁
      ≡ SAT.orBool left₂ right₂
    congruence refl refl =
      refl

    symmetry :
      ∀ {A : Set} {left right : A} →
      left ≡ right →
      right ≡ left
    symmetry refl =
      refl

    transitive :
      ∀ {A : Set} {left middle right : A} →
      left ≡ middle →
      middle ≡ right →
      left ≡ right
    transitive refl refl =
      refl

------------------------------------------------------------------------
-- The root decision is determined by the two child decisions, but recursively
-- materializing that law yields 2^n leaves.
------------------------------------------------------------------------

record ShannonSemanticAuthorityBoundary : Set where
  constructor shannon-semantic-authority-boundary
  field
    exactSATSemanticLawDerived : Bool
    lawUsesOnlyCorrectnessNotTrajectoryEncoding : Bool
    naiveRecursiveExpansionHasTwoPowerNLeaves : Bool
    polynomialSizeGlobalClosureDerived : Bool
    satNotInPDerived : Bool

canonicalShannonSemanticAuthorityBoundary :
  ShannonSemanticAuthorityBoundary
canonicalShannonSemanticAuthorityBoundary =
  shannon-semantic-authority-boundary
    true
    true
    true
    false
    false

------------------------------------------------------------------------
-- Research consequence.
--
-- P11 now has at least one genuine SAT-specific, non-circular semantic law.
-- What remains open is not discovering ANY semantic structure; it is deriving
-- a reusable/global closure of this or another law whose representation and
-- construction cost are sub-expansion while remaining exact.
------------------------------------------------------------------------
