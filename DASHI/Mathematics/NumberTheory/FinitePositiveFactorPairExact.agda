module DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact where

------------------------------------------------------------------------
-- POSITIVE FACTOR PAIRS WITH PREDECESSOR DATA
--
-- Refine the existing proof-bearing factor-pair scan for positive r so the
-- quotient is represented as k = suc predecessor.  This is the exact finite
-- data shape used by the Erdos residual key.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (filter)
open import Data.Nat.Base using (_≤_)
open import Data.Nat.Divisibility using (_∣_; _∣?_)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteFactorPairDivisorSumExact as Factor
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

record PositiveFactorPair (r : Nat) : Set where
  constructor positiveFactorPair
  field
    divisor : Nat
    predecessor : Nat
    productExact : r ≡ suc predecessor * divisor

open PositiveFactorPair public

pairWeight : ∀ {r} → PositiveFactorPair r → Nat
pairWeight = divisor

positiveNotZero :
  ∀ {r : Nat} → suc zero ≤ r → r ≡ zero → ⊥
positiveNotZero positive refl = caseImpossible positive
  where
  caseImpossible : suc zero ≤ zero → ⊥
  caseImpossible ()

positiveFactorPairsFrom :
  (r : Nat) → suc zero ≤ r → List Nat → List (PositiveFactorPair r)
positiveFactorPairsFrom r positive [] = []
positiveFactorPairsFrom r positive (d ∷ ds) with d ∣? r
... | no _ = positiveFactorPairsFrom r positive ds
... | yes dividesProof with _∣_.quotient dividesProof
...   | zero =
  ⊥-elim
    (positiveNotZero positive
      (trans (_∣_.equality dividesProof) refl))
...   | suc predecessor =
  positiveFactorPair d predecessor (_∣_.equality dividesProof)
  ∷ positiveFactorPairsFrom r positive ds

positiveFactorPairs :
  (r : Nat) → suc zero ≤ r → List (PositiveFactorPair r)
positiveFactorPairs r positive =
  positiveFactorPairsFrom r positive (Hecke.oneTo r)

positiveFactorPairWeightSum :
  (r : Nat) → (positive : suc zero ≤ r) → Nat
positiveFactorPairWeightSum r positive =
  Reindex.foldNat pairWeight (positiveFactorPairs r positive)

------------------------------------------------------------------------
-- Refinement preserves the old factor-pair weighted fold exactly.
------------------------------------------------------------------------

positivePairsFromWeightEqualsFactorPairsFrom :
  (r : Nat) (positive : suc zero ≤ r) (candidates : List Nat) →
  Reindex.foldNat pairWeight
    (positiveFactorPairsFrom r positive candidates)
  ≡ Reindex.foldNat Factor.factorWeight
    (Factor.factorPairsFrom r candidates)
positivePairsFromWeightEqualsFactorPairsFrom r positive [] = refl
positivePairsFromWeightEqualsFactorPairsFrom r positive (d ∷ ds)
  with d ∣? r
... | no _ = positivePairsFromWeightEqualsFactorPairsFrom r positive ds
... | yes dividesProof with _∣_.quotient dividesProof
...   | zero =
  ⊥-elim
    (positiveNotZero positive
      (trans (_∣_.equality dividesProof) refl))
...   | suc predecessor =
  cong (d +_)
    (positivePairsFromWeightEqualsFactorPairsFrom r positive ds)

positiveFactorPairWeightSumEqualsFactor :
  (r : Nat) (positive : suc zero ≤ r) →
  positiveFactorPairWeightSum r positive ≡ Factor.factorPairWeightSum r
positiveFactorPairWeightSumEqualsFactor r positive =
  positivePairsFromWeightEqualsFactorPairsFrom
    r positive (Hecke.oneTo r)

------------------------------------------------------------------------
-- No proof evidence enters residual identity: predecessor is ordinary Nat.
------------------------------------------------------------------------
