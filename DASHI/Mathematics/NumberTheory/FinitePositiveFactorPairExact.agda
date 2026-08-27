module DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact where

------------------------------------------------------------------------
-- POSITIVE FACTOR PAIRS WITH PREDECESSOR DATA
--
-- Refine the existing proof-bearing factor-pair scan for positive r so the
-- quotient is represented as k = suc predecessor.  The divisor also carries
-- its positive-prefix bounds 1 ≤ v ≤ r, needed only for later finite-index
-- transport; these proofs are not residual-key identity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.List.Relation.Unary.All as All
open import Data.Nat.Base using (_≤_; _<_)
open import Data.Nat.Divisibility using (_∣_; _∣?_; divides)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteFactorPairDivisorSumExact as Factor
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as OneTo
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

record PositiveFactorPair (r : Nat) : Set where
  constructor positiveFactorPair
  field
    divisor : Nat
    divisorPositive : suc zero ≤ divisor
    divisorBound : divisor ≤ r
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

------------------------------------------------------------------------
-- Quotient/predecessor order bounds used by residual finite enumeration.

copiesBoundByProduct :
  ∀ {r : Nat} (pair : PositiveFactorPair r) →
  suc (predecessor pair) ≤ r
copiesBoundByProduct
  (positiveFactorPair zero () divisorBound predecessor productExact)
copiesBoundByProduct
  (positiveFactorPair (suc divisorPredecessor)
    divisorPositive divisorBound predecessor productExact) =
  subst
    (λ target → suc predecessor ≤ target)
    (sym productExact)
    (NatP.m≤m*n (suc predecessor) (suc divisorPredecessor))

predecessorBelowProduct :
  ∀ {r : Nat} (pair : PositiveFactorPair r) →
  predecessor pair < r
predecessorBelowProduct pair =
  NatP.<-≤-trans
    (NatP.n<1+n (predecessor pair))
    (copiesBoundByProduct pair)

------------------------------------------------------------------------
-- Executable divisibility refinement.

positiveFactorPairsFrom :
  (r : Nat) →
  suc zero ≤ r →
  (candidates : List Nat) →
  All.All (λ d → (suc zero ≤ d) × (d ≤ r)) candidates →
  List (PositiveFactorPair r)
positiveFactorPairsFrom r positive [] All.[] = []
positiveFactorPairsFrom r positive (d ∷ ds) (All._∷_ bounds rest)
  with d ∣? r
... | no _ = positiveFactorPairsFrom r positive ds rest
... | yes dividesProof with _∣_.quotient dividesProof
...   | zero =
  ⊥-elim
    (positiveNotZero positive
      (trans (_∣_.equality dividesProof) refl))
...   | suc predecessor =
  positiveFactorPair
    d (proj₁ bounds) (proj₂ bounds)
    predecessor (_∣_.equality dividesProof)
  ∷ positiveFactorPairsFrom r positive ds rest

positiveFactorPairs :
  (r : Nat) → suc zero ≤ r → List (PositiveFactorPair r)
positiveFactorPairs r positive =
  positiveFactorPairsFrom r positive
    (Hecke.oneTo r) (OneTo.oneToAllBounds r)

positiveFactorPairWeightSum :
  (r : Nat) → (positive : suc zero ≤ r) → Nat
positiveFactorPairWeightSum r positive =
  Reindex.foldNat pairWeight (positiveFactorPairs r positive)

------------------------------------------------------------------------
-- Refinement preserves the old factor-pair weighted fold exactly.
------------------------------------------------------------------------

positivePairsFromWeightEqualsFactorPairsFrom :
  (r : Nat) (positive : suc zero ≤ r)
  (candidates : List Nat)
  (bounds : All.All (λ d → (suc zero ≤ d) × (d ≤ r)) candidates) →
  Reindex.foldNat pairWeight
    (positiveFactorPairsFrom r positive candidates bounds)
  ≡ Reindex.foldNat Factor.factorWeight
    (Factor.factorPairsFrom r candidates)
positivePairsFromWeightEqualsFactorPairsFrom r positive [] All.[] = refl
positivePairsFromWeightEqualsFactorPairsFrom
    r positive (d ∷ ds) (All._∷_ bounds rest)
  with d ∣? r
... | no _ =
  positivePairsFromWeightEqualsFactorPairsFrom r positive ds rest
... | yes dividesProof with _∣_.quotient dividesProof
...   | zero =
  ⊥-elim
    (positiveNotZero positive
      (trans (_∣_.equality dividesProof) refl))
...   | suc predecessor =
  cong (d +_)
    (positivePairsFromWeightEqualsFactorPairsFrom r positive ds rest)

positiveFactorPairWeightSumEqualsFactor :
  (r : Nat) (positive : suc zero ≤ r) →
  positiveFactorPairWeightSum r positive ≡ Factor.factorPairWeightSum r
positiveFactorPairWeightSumEqualsFactor r positive =
  positivePairsFromWeightEqualsFactorPairsFrom
    r positive (Hecke.oneTo r) (OneTo.oneToAllBounds r)

------------------------------------------------------------------------
-- Coordinate completeness of the proof-bearing scan.
--
-- The conclusion deliberately identifies only divisor/predecessor coordinates;
-- equality of proof fields is neither needed nor used by residual identity.

positiveFactorPairsFromCoordinatesComplete :
  (r : Nat) (positive : suc zero ≤ r)
  (candidates : List Nat)
  (bounds : All.All (λ d → (suc zero ≤ d) × (d ≤ r)) candidates) →
  ∀ {d predecessor : Nat} →
  d ∈ candidates →
  r ≡ suc predecessor * d →
  Σ (PositiveFactorPair r) λ pair →
    (pair ∈ positiveFactorPairsFrom r positive candidates bounds)
    × ((divisor pair ≡ d) × (predecessor pair ≡ predecessor))
positiveFactorPairsFromCoordinatesComplete r positive [] All.[] () product
positiveFactorPairsFromCoordinatesComplete
    r positive (zero ∷ ds) (All._∷_ bounds rest) member product =
  ⊥-elim (zeroCannotBePositive (proj₁ bounds))
  where
  zeroCannotBePositive : suc zero ≤ zero → ⊥
  zeroCannotBePositive ()
positiveFactorPairsFromCoordinatesComplete
    r positive (suc d ∷ ds) (All._∷_ bounds rest)
    {predecessor = predecessor} (Any.here refl) product
  with suc d ∣? r
... | no notDivides =
  ⊥-elim (notDivides (divides (suc predecessor) product))
... | yes dividesProof with _∣_.quotient dividesProof
...   | zero =
  ⊥-elim
    (positiveNotZero positive
      (trans (_∣_.equality dividesProof) refl))
...   | suc scannedPredecessor =
  selected
  , (Any.here refl
  , (refl , predecessorExact))
  where
  selected : PositiveFactorPair r
  selected =
    positiveFactorPair
      (suc d) (proj₁ bounds) (proj₂ bounds)
      scannedPredecessor (_∣_.equality dividesProof)

  quotientExact :
    suc scannedPredecessor ≡ suc predecessor
  quotientExact =
    NatP.*-cancelʳ-≡
      (suc scannedPredecessor)
      (suc predecessor)
      (suc d)
      (trans (sym (_∣_.equality dividesProof)) product)

  predecessorExact : scannedPredecessor ≡ predecessor
  predecessorExact = NatP.suc-injective quotientExact
positiveFactorPairsFromCoordinatesComplete
    r positive (suc candidate ∷ ds) (All._∷_ bounds rest)
    {d = d} {predecessor = predecessor} (Any.there member) product
  with suc candidate ∣? r
... | no _ =
  positiveFactorPairsFromCoordinatesComplete
    r positive ds rest member product
... | yes dividesProof with _∣_.quotient dividesProof
...   | zero =
  ⊥-elim
    (positiveNotZero positive
      (trans (_∣_.equality dividesProof) refl))
...   | suc scannedPredecessor
  with positiveFactorPairsFromCoordinatesComplete
         r positive ds rest member product
...     | pair , pairMember , coordinates =
  pair , (Any.there pairMember , coordinates)

positiveFactorPairCoordinatesComplete :
  (r : Nat) (positive : suc zero ≤ r) →
  ∀ {d predecessor : Nat} →
  suc zero ≤ d →
  d ≤ r →
  r ≡ suc predecessor * d →
  Σ (PositiveFactorPair r) λ pair →
    (pair ∈ positiveFactorPairs r positive)
    × ((divisor pair ≡ d) × (predecessor pair ≡ predecessor))
positiveFactorPairCoordinatesComplete r positive
    {d} {predecessor} dPositive dBound product =
  positiveFactorPairsFromCoordinatesComplete
    r positive
    (Hecke.oneTo r)
    (OneTo.oneToAllBounds r)
    (OneTo.oneToComplete dPositive dBound)
    product

------------------------------------------------------------------------
-- No proof evidence enters residual identity: predecessor is ordinary Nat.
------------------------------------------------------------------------
