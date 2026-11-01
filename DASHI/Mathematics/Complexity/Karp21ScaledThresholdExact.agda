module DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact where

------------------------------------------------------------------------
-- KARP 1972 E20: a ceiling-FREE integer-threshold reduction.
--
-- Given the original signed PARTITION numbers c_i, assign the complete
-- graph signed edge weights 4*c_i*c_j, and threshold T*T, where
-- T = sum_i c_i.  For T /= 0 the threshold is strictly positive.
-- The standard Karp target accepts signed integer edge weights; this
-- scaled variant avoids the round-to-ceiling step in the decision iff.
--
-- This owner proves the *universal algebraic and ordered* witness iff for
-- every signed selection. The graph's binary serializer, polynomial
-- machine-time map, positive-threshold proof for T /= 0 and T=0 fixed
-- YES-output construction are separate exact obligations.
--
-- Provenance: R. Karp (1972), DOI 10.1007/978-1-4684-2001-2_9.
-- DASHI's original signed complete-graph sum is in
-- Karp21PartitionCutQuadraticExact; square nonnegativity is REUSED
-- from the earlier ContractionForcesQuadraticStrong owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Data.Product using (_×_)
import Data.Integer as Int
open Int using (ℤ; _+_; _-_; _*_; _≤_)
import Data.Integer.Properties as IntP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21PartitionCutQuadraticExact as E20
import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as Square

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; _⊗_; ⊝_; solve)

SignedSelection : Set
SignedSelection = List (ℤ × Bool)

-- Score uses 4-times the ORIGINAL signed weighted complete graph's
-- crossing-edge sum. The new MAXCUT encoding will store 4*c_i*c_j
-- for every unordered pair.
scaledCutScore : SignedSelection → ℤ
scaledCutScore xs = (Int.+ 4) * E20.completeGraphCut xs

total : SignedSelection → ℤ
total = E20.signedTotal

thresholdSquare : SignedSelection → ℤ
thresholdSquare xs = total xs * total xs

balanced : SignedSelection → Set
balanced xs = E20.leftTotal xs ≡ E20.rightTotal xs

localTotal : SignedSelection → ℤ
localTotal xs = E20.leftTotal xs + E20.rightTotal xs

difference : SignedSelection → ℤ
difference xs = E20.leftTotal xs - E20.rightTotal xs

squaredReassociation : (t d : ℤ) →
  (t * t - d * d) + d * d ≡ t * t
squaredReassociation t d =
  RingZ.solve 2
    (λ t d →
      (((t ⊗ t) ⊕ (⊝ (d ⊗ d))) ⊕ (d ⊗ d)
      , t ⊗ t))
    refl t d

squareSubtractBound :
  (t d : ℤ) →
  (t * t - d * d) ≤ (t * t)
squareSubtractBound t d =
  subst
    (λ upper → (t * t - d * d) ≤ upper)
    (squaredReassociation t d)
    (IntP.i≤i+j
      (t * t - d * d)
      (d * d)
      {{Int.nonNegative (Square.squareNonnegative d)}})

scaledScoreBelowLocalSquare :
  (xs : SignedSelection) →
  scaledCutScore xs ≤ localTotal xs * localTotal xs
scaledScoreBelowLocalSquare xs =
  subst
    (λ left → left ≤ localTotal xs * localTotal xs)
    (sym (E20.completeGraphCutQuadratic xs))
    (squareSubtractBound (localTotal xs) (difference xs))

scaledScoreBelowSquare :
  (xs : SignedSelection) →
  scaledCutScore xs ≤ thresholdSquare xs
scaledScoreBelowSquare xs =
  subst
    (λ upper → scaledCutScore xs ≤ upper)
    (sym (cong (λ t → t * t) (E20.signedTotalDecomposes xs)))
    (scaledScoreBelowLocalSquare xs)

balancedImpliesScaledThreshold :
  (xs : SignedSelection) →
  balanced xs →
  thresholdSquare xs ≤ scaledCutScore xs
balancedImpliesScaledThreshold xs eq =
  IntP.≤-reflexive
    (sym
      (trans
        (E20.balancedSelectionImpliesExactMaximum xs eq)
        (sym (cong (λ t → t * t) (E20.signedTotalDecomposes xs)))))

scaledThresholdImpliesBalanced :
  (xs : SignedSelection) →
  thresholdSquare xs ≤ scaledCutScore xs →
  balanced xs
scaledThresholdImpliesBalanced xs accepted =
  E20.exactMaximumImpliesBalancedSelection xs
    (trans
      (IntP.≤-antisym (scaledScoreBelowSquare xs) accepted)
      (cong (λ t → t * t) (E20.signedTotalDecomposes xs)))

scaledThresholdIffBalanced :
  (xs : SignedSelection) →
  PR.Iff
    (balanced xs)
    (thresholdSquare xs ≤ scaledCutScore xs)
scaledThresholdIffBalanced xs =
  PR.iff
    (balancedImpliesScaledThreshold xs)
    (scaledThresholdImpliesBalanced xs)
