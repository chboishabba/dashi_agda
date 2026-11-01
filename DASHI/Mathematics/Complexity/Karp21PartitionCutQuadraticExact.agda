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
