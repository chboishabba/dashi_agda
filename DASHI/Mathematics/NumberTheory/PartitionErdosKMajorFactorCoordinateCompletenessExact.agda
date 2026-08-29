module DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateCompletenessExact where

------------------------------------------------------------------------
-- COORDINATE COMPLETENESS OF THE K-MAJOR FACTOR SCAN
--
-- Every positive pair (k,v) with k<=n, v<=n and k*v<=n occurs in the exact
-- k-major finite carrier.  As in FinitePositiveFactorPairExact, the theorem
-- recovers ordinary coordinates and list membership rather than identifying
-- proof fields.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.List.Relation.Unary.All as All
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as OneTo
import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateExact as KMajor

coordinatesForCopiesComplete :
  (n copies : Nat) →
  (copiesPositive : suc zero ≤ copies) →
  (copiesBound : copies ≤ n) →
  (divisors : List Nat) →
  (bounds : All.All (λ v → (suc zero ≤ v) × (v ≤ n)) divisors) →
  ∀ {divisor : Nat} →
  divisor ∈ divisors →
  copies * divisor ≤ n →
  Σ (KMajor.KMajorFactorCoordinate n) λ coordinate →
    (coordinate ∈
      KMajor.coordinatesForCopies
        n copies copiesPositive copiesBound divisors bounds)
    × ((KMajor.copies coordinate ≡ copies)
    × (KMajor.divisor coordinate ≡ divisor))
coordinatesForCopiesComplete
    n copies copiesPositive copiesBound [] All.[] () productBound
coordinatesForCopiesComplete
    n copies copiesPositive copiesBound
    (candidate ∷ divisors) (All._∷_ candidateBounds rest)
    {divisor} (Any.here equality) productBound
  with equality
... | refl with (copies * candidate) NatP.≤? n
...   | yes scannedBound =
  KMajor.kMajorFactorCoordinate
    copies candidate copiesPositive copiesBound
    (proj₁ candidateBounds) (proj₂ candidateBounds) scannedBound
  , (Any.here refl , (refl , refl))
...   | no notBound = ⊥-elim (notBound productBound)
coordinatesForCopiesComplete
    n copies copiesPositive copiesBound
    (candidate ∷ divisors) (All._∷_ candidateBounds rest)
    {divisor} (Any.there member) productBound
  with (copies * candidate) NatP.≤? n
... | yes scannedBound
  with coordinatesForCopiesComplete
         n copies copiesPositive copiesBound
         divisors rest member productBound
...   | coordinate , coordinateMember , coordinates =
  coordinate , (Any.there coordinateMember , coordinates)
... | no notBound =
  coordinatesForCopiesComplete
    n copies copiesPositive copiesBound
    divisors rest member productBound

kMajorFactorCoordinatesFromComplete :
  (n : Nat) →
  (copiesList : List Nat) →
  (bounds : All.All (λ k → (suc zero ≤ k) × (k ≤ n)) copiesList) →
  ∀ {copies divisor : Nat} →
  copies ∈ copiesList →
  divisor ∈ Hecke.oneTo n →
  copies * divisor ≤ n →
  Σ (KMajor.KMajorFactorCoordinate n) λ coordinate →
    (coordinate ∈ KMajor.kMajorFactorCoordinatesFrom n copiesList bounds)
    × ((KMajor.copies coordinate ≡ copies)
    × (KMajor.divisor coordinate ≡ divisor))
kMajorFactorCoordinatesFromComplete n [] All.[] () divisorMember productBound
kMajorFactorCoordinatesFromComplete
    n (candidate ∷ restCopies) (All._∷_ candidateBounds restBounds)
    {copies} {divisor} (Any.here equality) divisorMember productBound
  with equality
... | refl
  with coordinatesForCopiesComplete
         n candidate
         (proj₁ candidateBounds) (proj₂ candidateBounds)
         (Hecke.oneTo n) (OneTo.oneToAllBounds n)
         divisorMember productBound
...   | coordinate , coordinateMember , coordinates =
  coordinate ,
    (Product.appendMemberLeft coordinateMember , coordinates)
kMajorFactorCoordinatesFromComplete
    n (candidate ∷ restCopies) (All._∷_ candidateBounds restBounds)
    {copies} {divisor} (Any.there copiesMember) divisorMember productBound
  with kMajorFactorCoordinatesFromComplete
         n restCopies restBounds
         copiesMember divisorMember productBound
... | coordinate , coordinateMember , coordinates =
  coordinate ,
    (Product.appendMemberRight
      (KMajor.coordinatesForCopies
        n candidate
        (proj₁ candidateBounds) (proj₂ candidateBounds)
        (Hecke.oneTo n) (OneTo.oneToAllBounds n))
      coordinateMember
    , coordinates)

kMajorFactorCoordinatesComplete :
  (n : Nat) →
  ∀ {copies divisor : Nat} →
  suc zero ≤ copies → copies ≤ n →
  suc zero ≤ divisor → divisor ≤ n →
  copies * divisor ≤ n →
  Σ (KMajor.KMajorFactorCoordinate n) λ coordinate →
    (coordinate ∈ KMajor.kMajorFactorCoordinates n)
    × ((KMajor.copies coordinate ≡ copies)
    × (KMajor.divisor coordinate ≡ divisor))
kMajorFactorCoordinatesComplete
    n {copies} {divisor}
    copiesPositive copiesBound divisorPositive divisorBound productBound =
  kMajorFactorCoordinatesFromComplete
    n
    (Hecke.oneTo n)
    (OneTo.oneToAllBounds n)
    (OneTo.oneToComplete copiesPositive copiesBound)
    (OneTo.oneToComplete divisorPositive divisorBound)
    productBound

------------------------------------------------------------------------
-- The reverse direction is definitionally available from each carrier record:
-- positivity and the product cutoff are stored fields.  Thus the k-major scan
-- now has an exact source-level completeness theorem ready for uniqueness and
-- permutation with the residual-major factor presentation.
------------------------------------------------------------------------
