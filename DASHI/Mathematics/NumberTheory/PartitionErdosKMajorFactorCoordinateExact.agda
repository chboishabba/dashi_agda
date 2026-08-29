module DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateExact where

------------------------------------------------------------------------
-- K-MAJOR POSITIVE FACTOR COORDINATES
--
-- Erdős's analytic estimate wants the classical factor coordinates ordered by
-- quotient/copy count k first and divisor v second:
--
--   1 <= k, 1 <= v, k*v <= n.
--
-- This owner introduces exactly that finite carrier.  It does not replace the
-- existing residual-major PositiveFactorPair scan: every coordinate decodes
-- back to that proof-bearing factor-pair type at residual r = k*v.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.List.Base using (_++_)
import Data.List.Relation.Unary.All as All
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as OneTo
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor

record KMajorFactorCoordinate (n : Nat) : Set where
  constructor kMajorFactorCoordinate
  field
    copies : Nat
    divisor : Nat
    copiesPositive : suc zero ≤ copies
    copiesBound : copies ≤ n
    divisorPositive : suc zero ≤ divisor
    divisorBound : divisor ≤ n
    productBound : copies * divisor ≤ n

open KMajorFactorCoordinate public

copiesPredecessor : ∀ {n} → KMajorFactorCoordinate n → Nat
copiesPredecessor
  (kMajorFactorCoordinate zero divisor () copiesBound
    divisorPositive divisorBound productBound)
copiesPredecessor
  (kMajorFactorCoordinate (suc predecessor) divisor
    copiesPositive copiesBound divisorPositive divisorBound productBound) =
  predecessor

copiesIsSuccessor :
  ∀ {n} (coordinate : KMajorFactorCoordinate n) →
  copies coordinate ≡ suc (copiesPredecessor coordinate)
copiesIsSuccessor
  (kMajorFactorCoordinate zero divisor () copiesBound
    divisorPositive divisorBound productBound)
copiesIsSuccessor
  (kMajorFactorCoordinate (suc predecessor) divisor
    copiesPositive copiesBound divisorPositive divisorBound productBound) = refl

residual : ∀ {n} → KMajorFactorCoordinate n → Nat
residual coordinate = copies coordinate * divisor coordinate

residualPositive :
  ∀ {n} (coordinate : KMajorFactorCoordinate n) →
  suc zero ≤ residual coordinate
residualPositive
  (kMajorFactorCoordinate zero divisor () copiesBound
    divisorPositive divisorBound productBound)
residualPositive
  (kMajorFactorCoordinate (suc copiesPredecessor) zero
    copiesPositive copiesBound () divisorBound productBound)
residualPositive
  (kMajorFactorCoordinate (suc copiesPredecessor) (suc divisorPredecessor)
    copiesPositive copiesBound divisorPositive divisorBound productBound) =
  NatP.≤-trans
    copiesPositive
    (NatP.m≤m*n (suc copiesPredecessor) (suc divisorPredecessor))

asPositiveFactorPair :
  ∀ {n} (coordinate : KMajorFactorCoordinate n) →
  Factor.PositiveFactorPair (residual coordinate)
asPositiveFactorPair
  (kMajorFactorCoordinate zero divisor () copiesBound
    divisorPositive divisorBound productBound)
asPositiveFactorPair
  (kMajorFactorCoordinate (suc copiesPredecessor) zero
    copiesPositive copiesBound () divisorBound productBound)
asPositiveFactorPair
  (kMajorFactorCoordinate (suc copiesPredecessor) (suc divisorPredecessor)
    copiesPositive copiesBound divisorPositive divisorBound productBound) =
  Factor.positiveFactorPair
    (suc divisorPredecessor)
    divisorPositive
    divisor≤product
    copiesPredecessor
    refl
  where
  divisor≤product :
    suc divisorPredecessor
    ≤ suc copiesPredecessor * suc divisorPredecessor
  divisor≤product =
    NatP.≤-trans
      (NatP.m≤m*n (suc divisorPredecessor) (suc copiesPredecessor))
      (NatP.≤-reflexive
        (NatP.*-comm
          (suc divisorPredecessor)
          (suc copiesPredecessor)))

------------------------------------------------------------------------
-- Executable k-major scan.  `oneTo n` supplies positivity/boundedness of both
-- coordinates; the only filter is the product cutoff k*v <= n.
------------------------------------------------------------------------

coordinatesForCopies :
  (n copies : Nat) →
  suc zero ≤ copies → copies ≤ n →
  (divisors : List Nat) →
  All.All (λ v → (suc zero ≤ v) × (v ≤ n)) divisors →
  List (KMajorFactorCoordinate n)
coordinatesForCopies n copies copiesPositive copiesBound [] All.[] = []
coordinatesForCopies n copies copiesPositive copiesBound
    (divisor ∷ divisors) (All._∷_ divisorBounds rest)
  with (copies * divisor) NatP.≤? n
... | yes productBound =
  kMajorFactorCoordinate
    copies divisor copiesPositive copiesBound
    (proj₁ divisorBounds) (proj₂ divisorBounds) productBound
  ∷ coordinatesForCopies
      n copies copiesPositive copiesBound divisors rest
... | no _ =
  coordinatesForCopies
    n copies copiesPositive copiesBound divisors rest

kMajorFactorCoordinatesFrom :
  (n : Nat) →
  (copiesList : List Nat) →
  All.All (λ k → (suc zero ≤ k) × (k ≤ n)) copiesList →
  List (KMajorFactorCoordinate n)
kMajorFactorCoordinatesFrom n [] All.[] = []
kMajorFactorCoordinatesFrom n (copies ∷ restCopies)
    (All._∷_ copiesBounds restBounds) =
  coordinatesForCopies
    n copies (proj₁ copiesBounds) (proj₂ copiesBounds)
    (Hecke.oneTo n) (OneTo.oneToAllBounds n)
  ++ kMajorFactorCoordinatesFrom n restCopies restBounds

kMajorFactorCoordinates : (n : Nat) → List (KMajorFactorCoordinate n)
kMajorFactorCoordinates n =
  kMajorFactorCoordinatesFrom
    n (Hecke.oneTo n) (OneTo.oneToAllBounds n)

------------------------------------------------------------------------
-- This owner deliberately stops before uniqueness/completeness/permutation.
-- Those are downstream exact finite-list receipts.  The carrier itself is
-- already Basel-friendly: copies is the outer coordinate and divisor is the
-- inner coordinate.
------------------------------------------------------------------------
