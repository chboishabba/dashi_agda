module DASHI.Mathematics.NumberTheory.PartitionErdosKMajorPositiveFactorBridgeExact where

------------------------------------------------------------------------
-- K-MAJOR / RESIDUAL-MAJOR FACTOR COORDINATE BRIDGE
--
-- The new Basel-friendly carrier and the pre-existing PositiveFactorPair scan
-- encode the same ordinary coordinates.  This owner proves both directions at
-- the membership/coordinate level while deliberately avoiding equality of
-- proof fields.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans; subst)

import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateExact as KMajor
import DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateCompletenessExact as Complete

------------------------------------------------------------------------
-- Every k-major coordinate selects the corresponding ordinary divisor/copies
-- coordinates in the existing residual-major PositiveFactorPair scan.

kMajorCoordinateToPositiveFactorScan :
  ∀ {n : Nat} (coordinate : KMajor.KMajorFactorCoordinate n) →
  Σ (Factor.PositiveFactorPair (KMajor.residual coordinate)) λ pair →
    (pair ∈ Factor.positiveFactorPairs
      (KMajor.residual coordinate)
      (KMajor.residualPositive coordinate))
    × ((Factor.divisor pair ≡ KMajor.divisor coordinate)
    × (Factor.predecessor pair ≡ KMajor.copiesPredecessor coordinate))
kMajorCoordinateToPositiveFactorScan coordinate =
  Factor.positiveFactorPairCoordinatesComplete
    (KMajor.residual coordinate)
    (KMajor.residualPositive coordinate)
    (KMajor.divisorPositive coordinate)
    (Factor.divisorBound (KMajor.asPositiveFactorPair coordinate))
    (Factor.productExact (KMajor.asPositiveFactorPair coordinate))

------------------------------------------------------------------------
-- Conversely any positive factor pair r=k*v with r<=n occurs in the k-major
-- scan.  The returned coordinate recovers k, v and the literal residual r.

positiveFactorToKMajorCoordinate :
  ∀ {n r : Nat} →
  r ≤ n →
  (pair : Factor.PositiveFactorPair r) →
  Σ (KMajor.KMajorFactorCoordinate n) λ coordinate →
    (coordinate ∈ KMajor.kMajorFactorCoordinates n)
    × ((KMajor.copies coordinate ≡ suc (Factor.predecessor pair))
    × ((KMajor.divisor coordinate ≡ Factor.divisor pair)
    × (KMajor.residual coordinate ≡ r)))
positiveFactorToKMajorCoordinate {n} {r} rBound pair
  with Complete.kMajorFactorCoordinatesComplete
         n
         (NatP.≤-trans
           (NatP.n<1+n (Factor.predecessor pair))
           (Factor.copiesBoundByProduct pair))
         (NatP.≤-trans (Factor.copiesBoundByProduct pair) rBound)
         (Factor.divisorPositive pair)
         (NatP.≤-trans (Factor.divisorBound pair) rBound)
         productBound
... | coordinate , coordinateMember , copiesExact , divisorExact =
  coordinate ,
    (coordinateMember
    , (copiesExact
    , (divisorExact
    , residualExact)))
  where
  residualExact : KMajor.residual coordinate ≡ r
  residualExact =
    trans
      (cong₂ _*_ copiesExact divisorExact)
      (sym (Factor.productExact pair))
  where
  productBound :
    suc (Factor.predecessor pair) * Factor.divisor pair ≤ n
  productBound =
    subst
      (λ product → product ≤ n)
      (Factor.productExact pair)
      rBound

------------------------------------------------------------------------
-- These two coordinate-completeness directions are the arithmetic content of
-- the reindex.  A literal list permutation can now be packaged over a common
-- proof-free coordinate key without introducing any new number theory.
------------------------------------------------------------------------
