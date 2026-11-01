module DASHI.Mathematics.Complexity.Karp21PartitionCutQuadraticExact where

------------------------------------------------------------------------
-- SOURCE / ORIGINAL OWNERS
-- Richard M. Karp, "Reducibility Among Combinatorial Problems" (1972),
-- p. 100, DOI: 10.1007/978-1-4684-2001-2_9,
-- PARTITION -> MAX CUT on signed integer weights c_i * c_j.
--
-- DASHI reuses its earlier exact integer ring-solver proof machinery
-- (e.g. DASHI.Physics.QuadraticPolarizationCoreInstance) and proves the
-- unconditional polynomial identity on the actual ℤ scalar carrier.
-- This is *not* the missing inequality/threshold iff, complete-graph
-- cross-edge enumeration or polynomial bit-complexity certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _-_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; _⊗_; ⊝_; solve)

-- Both sides receive a total over the same list of signed weights.
-- The Boolean label is a *selection witness*, not an NP-completeness
-- assertion and not a procedure for finding a good selection.
signedTotal : List (ℤ × Bool) → ℤ
signedTotal [] = + 0
signedTotal ((x , side) ∷ xs) = x + signedTotal xs

leftTotal : List (ℤ × Bool) → ℤ
leftTotal [] = + 0
leftTotal ((x , true) ∷ xs) = x + leftTotal xs
leftTotal ((x , false) ∷ xs) = leftTotal xs

rightTotal : List (ℤ × Bool) → ℤ
rightTotal [] = + 0
rightTotal ((x , true) ∷ xs) = rightTotal xs
rightTotal ((x , false) ∷ xs) = x + rightTotal xs

sumAssociativity : (a b c : ℤ) →
  a + (b + c) ≡ (a + b) + c
sumAssociativity a b c =
  RingZ.solve 3
    (λ a b c → (a ⊕ (b ⊕ c) , (a ⊕ b) ⊕ c))
    refl a b c

sumInterchange : (a b c : ℤ) →
  a + (b + c) ≡ b + (a + c)
sumInterchange a b c =
  RingZ.solve 3
    (λ a b c → (a ⊕ (b ⊕ c) , b ⊕ (a ⊕ c)))
    refl a b c

signedTotalDecomposes :
  (items : List (ℤ × Bool)) →
  signedTotal items ≡ leftTotal items + rightTotal items
signedTotalDecomposes [] = refl
signedTotalDecomposes ((x , true) ∷ xs) =
  trans
    (cong (λ remainder → x + remainder) (signedTotalDecomposes xs))
    (sumAssociativity x (leftTotal xs) (rightTotal xs))
signedTotalDecomposes ((x , false) ∷ xs) =
  trans
    (cong (λ remainder → x + remainder) (signedTotalDecomposes xs))
    (sumInterchange x (leftTotal xs) (rightTotal xs))

-- The two exact formulations of the signed graph-cut product identity
-- used by the E20 integer threshold reduction.
partitionCutProductIdentity :
  (a b : ℤ) →
  (+ 4) * (a * b) ≡
  ((a + b) * (a + b)) - ((a - b) * (a - b))
partitionCutProductIdentity a b =
  RingZ.solve 2
    (λ a b →
      (Κ (+ 4) ⊗ (a ⊗ b)
      , ((a ⊕ b) ⊗ (a ⊕ b)) ⊕
        (⊝ ((a ⊕ (⊝ b)) ⊗ (a ⊕ (⊝ b))))))
    refl a b

-- For *every* signed instance and *every* selection, E20's arithmetic
-- agrees with the signed partition totals, independently of positivity.
partitionCutProductForSelection :
  (items : List (ℤ × Bool)) →
  (+ 4) * (leftTotal items * rightTotal items) ≡
  ((leftTotal items + rightTotal items) *
   (leftTotal items + rightTotal items)) -
  ((leftTotal items - rightTotal items) *
   (leftTotal items - rightTotal items))
partitionCutProductForSelection items =
  partitionCutProductIdentity (leftTotal items) (rightTotal items)


------------------------------------------------------------------------
-- Literal complete-graph weighted cut, represented as a triangular edge
-- enumeration. Each pair (head,tail) is counted EXACTLY ONCE. In
-- particular, no duplicate directed pairs or omitted off-diagonal pairs
-- are hidden in a closed-form definition of the objective.
------------------------------------------------------------------------

crossWith : ℤ → Bool → List (ℤ × Bool) → ℤ
crossWith x side [] = + 0
crossWith x true  ((y , true) ∷ xs) = crossWith x true xs
crossWith x true  ((y , false) ∷ xs) =
  (x * y) + crossWith x true xs
crossWith x false ((y , false) ∷ xs) = crossWith x false xs
crossWith x false ((y , true) ∷ xs) =
  (x * y) + crossWith x false xs

completeGraphCut : List (ℤ × Bool) → ℤ
completeGraphCut [] = + 0
completeGraphCut ((x , side) ∷ xs) =
  crossWith x side xs + completeGraphCut xs

crossStepRight : (x y right : ℤ) →
  (x * y) + (x * right) ≡ x * (y + right)
crossStepRight x y right =
  RingZ.solve 3
    (λ x y right →
      ((x ⊗ y) ⊕ (x ⊗ right)
      , x ⊗ (y ⊕ right)))
    refl x y right

crossStepLeft : (x y left : ℤ) →
  (x * y) + (x * left) ≡ x * (y + left)
crossStepLeft = crossStepRight

crossWithTrue :
  (x : ℤ) (items : List (ℤ × Bool)) →
  crossWith x true items ≡ x * rightTotal items
crossWithTrue x [] = refl
crossWithTrue x ((y , true) ∷ xs) =
  crossWithTrue x xs
crossWithTrue x ((y , false) ∷ xs) =
  trans
    (cong (λ tail → x * y + tail) (crossWithTrue x xs))
    (crossStepRight x y (rightTotal xs))

crossWithFalse :
  (x : ℤ) (items : List (ℤ × Bool)) →
  crossWith x false items ≡ x * leftTotal items
crossWithFalse x [] = refl
crossWithFalse x ((y , false) ∷ xs) =
  crossWithFalse x xs
crossWithFalse x ((y , true) ∷ xs) =
  trans
    (cong (λ tail → x * y + tail) (crossWithFalse x xs))
    (crossStepLeft x y (leftTotal xs))

cutStepTrue : (x left right : ℤ) →
  (x * right) + (left * right) ≡ (x + left) * right
cutStepTrue x left right =
  RingZ.solve 3
    (λ x left right →
      ((x ⊗ right) ⊕ (left ⊗ right)
      , (x ⊕ left) ⊗ right))
    refl x left right

cutStepFalse : (x left right : ℤ) →
  (x * left) + (left * right) ≡ left * (x + right)
cutStepFalse x left right =
  RingZ.solve 3
    (λ x left right →
      ((x ⊗ left) ⊕ (left ⊗ right)
      , left ⊗ (x ⊕ right)))
    refl x left right

completeGraphCutEqualsPartitionProduct :
  (items : List (ℤ × Bool)) →
  completeGraphCut items ≡ leftTotal items * rightTotal items
completeGraphCutEqualsPartitionProduct [] = refl
completeGraphCutEqualsPartitionProduct ((x , true) ∷ xs) =
  trans
    (cong (λ tail → crossWith x true xs + tail)
      (completeGraphCutEqualsPartitionProduct xs))
    (trans
      (cong (λ first → first + (leftTotal xs * rightTotal xs))
        (crossWithTrue x xs))
      (cutStepTrue x (leftTotal xs) (rightTotal xs)))
completeGraphCutEqualsPartitionProduct ((x , false) ∷ xs) =
  trans
    (cong (λ tail → crossWith x false xs + tail)
      (completeGraphCutEqualsPartitionProduct xs))
    (trans
      (cong (λ first → first + (leftTotal xs * rightTotal xs))
        (crossWithFalse x xs))
      (cutStepFalse x (leftTotal xs) (rightTotal xs)))

-- Actual E20 bridge: the cut is defined from crossing edges, not by
-- *assuming* it equals a product. This closes the universal scalar/graph
-- equality, but NOT the threshold iff or the encoded polynomial map.
completeGraphCutQuadratic :
  (items : List (ℤ × Bool)) →
  (+ 4) * completeGraphCut items ≡
  ((leftTotal items + rightTotal items) *
   (leftTotal items + rightTotal items)) -
  ((leftTotal items - rightTotal items) *
   (leftTotal items - rightTotal items))
completeGraphCutQuadratic items =
  trans
    (cong (λ weight → (+ 4) * weight)
      (completeGraphCutEqualsPartitionProduct items))
    (partitionCutProductForSelection items)
