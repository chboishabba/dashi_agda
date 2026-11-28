module DASHI.Mathematics.Complexity.PNotEqualsNPShannonRoutingDefectExact where

-- G105-G113: reuse the actual indexed Shannon restriction family.
-- No SAT oracle, cost certificate, or universal failure premise is added.
-- Source-level proof candidate; native kernel checking remains outstanding.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalFutureCongruenceExact as Future

Policy : ∀ {n : Nat} → SAT.BooleanFormula n → Set
Policy root =
  ∀ {r : Nat} {current : SAT.BooleanFormula (suc r)} →
  Family.RestrictionDerivation root current → Bool

child :
  ∀ {n r : Nat} {root : SAT.BooleanFormula n}
    {current : SAT.BooleanFormula (suc r)} →
  (b : Bool) → Family.RestrictionDerivation root current →
  Family.RestrictionDerivation root (SAT.restrictHead b current)
child false d = Family.restrictionFalse d
child true d = Family.restrictionTrue d

-- Score only the one routed terminal, not the entire restriction tree.
score :
  ∀ {n r : Nat} {root : SAT.BooleanFormula n}
    {current : SAT.BooleanFormula r} →
  Policy root → Family.RestrictionDerivation root current → Bool
score {r = zero} {current = current} c d =
  SAT.evaluate current Future.emptyAssignment
score {r = suc r} c d with c d
... | false = score c (Family.restrictionFalse d)
... | true = score c (Family.restrictionTrue d)

-- Every positive score gives an actual current-fibre witness.
scoreSound :
  ∀ {n r : Nat} {root : SAT.BooleanFormula n}
    {current : SAT.BooleanFormula r} →
  (c : Policy root) (d : Family.RestrictionDerivation root current) →
  score c d ≡ true → SAT.Satisfying current
scoreSound {r = zero} c d yes = SAT.satisfying Future.emptyAssignment yes
scoreSound {r = suc r} {current = current} c d yes with c d
... | false = SAT.liftFalse current
  (scoreSound c (Family.restrictionFalse d) yes)
... | true = SAT.liftTrue current
  (scoreSound c (Family.restrictionTrue d) yes)

-- A boundary is a rejected parent with a successful immediate child.
-- Since score follows exactly one child, that successful child is unchosen.
record Boundary {n : Nat} {root : SAT.BooleanFormula n}
                (c : Policy root) : Set where
  constructor boundary
  field
    remaining : Nat
    current : SAT.BooleanFormula (suc remaining)
    derivation : Family.RestrictionDerivation root current
    action : Bool
    parentRejected : score c derivation ≡ false
    childAccepted : score c (child action derivation) ≡ true

open Boundary public

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

-- Original restriction history is not erased by localization.
liftToRoot :
  ∀ {n r : Nat} {root : SAT.BooleanFormula n}
    {current : SAT.BooleanFormula r} →
  Family.RestrictionDerivation root current →
  SAT.Satisfying current → SAT.Satisfying root
liftToRoot Family.restrictionRoot w = w
liftToRoot (Family.restrictionFalse {current = parent} d) w =
  liftToRoot d (SAT.liftFalse parent w)
liftToRoot (Family.restrictionTrue {current = parent} d) w =
  liftToRoot d (SAT.liftTrue parent w)

boundaryWitness :
  ∀ {n : Nat} {root : SAT.BooleanFormula n} {c : Policy root} →
  (b : Boundary c) → SAT.Satisfying (current b)
boundaryWitness {c = c} (boundary r f d false no yes) =
  SAT.liftFalse f (scoreSound c (Family.restrictionFalse d) yes)
boundaryWitness {c = c} (boundary r f d true no yes) =
  SAT.liftTrue f (scoreSound c (Family.restrictionTrue d) yes)

boundaryRootWitness :
  ∀ {n : Nat} {root : SAT.BooleanFormula n} {c : Policy root} →
  Boundary c → SAT.Satisfying root
boundaryRootWitness b = liftToRoot (derivation b) (boundaryWitness b)

-- Constructive descent using the existing satisfiableSplits owner.
-- This is the structural proof, not the separate logarithmic-query algorithm.
locate :
  ∀ {n r : Nat} {root : SAT.BooleanFormula n}
    {current : SAT.BooleanFormula r} →
  (c : Policy root) (d : Family.RestrictionDerivation root current) →
  score c d ≡ false → SAT.Satisfying current → Boundary c
locate {r = zero} {current = current} c d no w =
  ⊥-elim (falseNotTrue
    (trans (sym no)
      (trans (SAT.evaluateExtensional current (λ ()))
             (SAT.evaluatesTrue w))))
locate {r = suc r} {current = current} c d no w
  with SAT.satisfiableSplits current w
... | inj₁ left with score c (Family.restrictionFalse d) in eq
...   | true = boundary r current d false no eq
...   | false = locate c (Family.restrictionFalse d) eq left
locate {r = suc r} {current = current} c d no w
  | inj₂ right with score c (Family.restrictionTrue d) in eq
...   | true = boundary r current d true no eq
...   | false = locate c (Family.restrictionTrue d) eq right

-- A globally defect-free policy is complete on every reachable restriction.
defectFreeComplete :
  ∀ {n r : Nat} {root : SAT.BooleanFormula n}
    {current : SAT.BooleanFormula r} →
  (c : Policy root) → (Boundary c → ⊥) →
  (d : Family.RestrictionDerivation root current) →
  SAT.Satisfying current → score c d ≡ true
defectFreeComplete c absent d w with score c d in eq
... | true = eq
... | false = ⊥-elim (absent (locate c d eq w))
