module DASHI.Information.PNFHistoryTimeVariableDimensionExact where

-- Fully dependent temporal hyperfabric: sample count and coordinate
-- dimension belong to EACH history/time source, not a global p.
-- This is essential for point-in-time financial universes and for
-- PNF predicates that enter/leave the admissible observation fibre.
--
-- At each (h,t), rows = suc(suc kAt(h,t)); columns = pAt(h,t).
-- A coordinate rechart between different p values is an independent
-- typed transport, not an implicit coercion of covariance matrices.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _∸_)
open import Agda.Builtin.String using (String)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (_≤_)

import DASHI.Algebra.Trit as Trit
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Indexed
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitGramAssembly as PSD
import DASHI.Information.PNFSampleMeanExact as Mean
import DASHI.Information.PNFCentredCovarianceExact as Centre
import DASHI.Information.PNFCovarianceQuadraticIdentityExact as Quadratic
import DASHI.Information.PNFFiniteRankNullityBridgeExact as Rank
import DASHI.Information.PNFHistoryTimeTernaryCovarianceFibreExact as Fixed

record HistoryTimeVariableDimensionFibre
  (K : Ring.ExactOrderedCommutativeRing)
  (depth : Nat) : Set₂ where
  field
    History : Set
    Time : Set
    fabric : Indexed.IndexedFabric Trit.Trit depth
    situatedAt : History → Time → Indexed.Situated fabric

    kAt : History → Time → Nat
    pAt : History → Time → Nat
    actualWindowAt :
      (h : History) → (t : Time) →
      Mean.ActualFiniteMean K
        (suc (suc (kAt h t))) (pAt h t)
    scaleAt :
      (h : History) → (t : Time) →
      Scalar.Scalar (Ring.orderedScalar K)
    scaleNonnegativeAt :
      (h : History) → (t : Time) →
      Scalar._≤_ (Ring.orderedScalar K)
        (Scalar.zero (Ring.orderedScalar K)) (scaleAt h t)
    sourceRefAt : History → Time → String
    consumerVersionAt : History → Time → Nat

open HistoryTimeVariableDimensionFibre public

variableCovarianceAt :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth : Nat} →
  (F : HistoryTimeVariableDimensionFibre K depth) →
  (h : History F) → (t : Time F) →
  Fin (pAt F h t) → Fin (pAt F h t) →
  Scalar.Scalar (Ring.orderedScalar K)
variableCovarianceAt K F h t =
  Centre.scaledCovariance K
    (Mean.source (actualWindowAt F h t))
    (scaleAt F h t)

variableCovarianceQuadraticAt :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth : Nat} →
  (F : HistoryTimeVariableDimensionFibre K depth) →
  (h : History F) → (t : Time F) →
  (Fin (pAt F h t) → Scalar.Scalar (Ring.orderedScalar K)) →
  Scalar.Scalar (Ring.orderedScalar K)
variableCovarianceQuadraticAt K F h t =
  Quadratic.covarianceOperatorQuadratic K
    (Mean.source (actualWindowAt F h t))
    (scaleAt F h t)

variableCovarianceSymmetricAt :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth : Nat} →
  (F : HistoryTimeVariableDimensionFibre K depth) →
  (h : History F) → (t : Time F) →
  (i j : Fin (pAt F h t)) →
  variableCovarianceAt K F h t i j ≡
  variableCovarianceAt K F h t j i
variableCovarianceSymmetricAt K F h t =
  Centre.scaledCovarianceSymmetric K
    (Mean.source (actualWindowAt F h t))
    (scaleAt F h t)

variableCovariancePSDAt :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : PSD.FiniteGramOrderAuthority K) →
  {depth : Nat} →
  (F : HistoryTimeVariableDimensionFibre K depth) →
  (h : History F) → (t : Time F) →
  (v : Fin (pAt F h t) →
    Scalar.Scalar (Ring.orderedScalar K)) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K))
    (variableCovarianceQuadraticAt K F h t v)
variableCovariancePSDAt K O F h t =
  Quadratic.covarianceOperatorPositiveSemidefinite K O
    (Mean.source (actualWindowAt F h t))
    (scaleAt F h t)
    (scaleNonnegativeAt F h t)

-- Reuses precisely the existing finite rank/nullity theorem interface.
-- It is *not* instantiated by balanced-ternary cardinality alone.
variableCovarianceForcedNullityAt :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : Rank.FiniteFieldRankNullityOwner K) →
  {depth : Nat} →
  (F : HistoryTimeVariableDimensionFibre K depth) →
  (h : History F) → (t : Time F) →
  (pAt F h t) ∸ suc (kAt F h t)
  ≤ Rank.nullity O
      (Rank.covarianceLinearMap K
        (actualWindowAt F h t) (scaleAt F h t))
variableCovarianceForcedNullityAt K O F h t =
  Rank.covarianceNullityAtLeastForcedLowerBound K O
    (actualWindowAt F h t) (scaleAt F h t)

-- An actual change of predicate/asset coordinates needs a typed map
-- plus proof of covariance compatibility. Equal ternary top-level
-- addresses are not themselves a matrix basis-change certificate.
record TemporalCoordinateTransport
  (K : Ring.ExactOrderedCommutativeRing)
  {depth : Nat}
  (F : HistoryTimeVariableDimensionFibre K depth)
  (h : History F)
  (before after : Time F) : Set₁ where
  field
    coordinateMap :
      Fin (pAt F h before) → Fin (pAt F h after)
    transportedCovarianceAgrees :
      (i j : Fin (pAt F h before)) →
      variableCovarianceAt K F h before i j ≡
      variableCovarianceAt K F h after
        (coordinateMap i) (coordinateMap j)

open TemporalCoordinateTransport public

-- Embed any earlier fixed-dimension time/history family into this
-- canonical dependent (n(t),p(t)) model. This is a true conservative
-- extension: the same fibre, source, window and consumer are retained.
fixedWindowAsVariableDimension :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : Fixed.HistoryTimeTernaryCovarianceFibre K depth k p) →
  HistoryTimeVariableDimensionFibre K depth
fixedWindowAsVariableDimension K {depth} {k} {p} F = record
  { History = Fixed.History F
  ; Time = Fixed.Time F
  ; fabric = Fixed.fabric F
  ; situatedAt = Fixed.situatedAt F
  ; kAt = λ _ _ → k
  ; pAt = λ _ _ → p
  ; actualWindowAt = Fixed.windowAt F
  ; scaleAt = Fixed.scaleAt F
  ; scaleNonnegativeAt = Fixed.scaleNonnegativeAt F
  ; sourceRefAt = Fixed.sourceReferenceAt F
  ; consumerVersionAt = Fixed.consumerVersionAt F
  }

fixedCovarianceIsVariableCovariance :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : Fixed.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (h : Fixed.History F) → (t : Fixed.Time F) →
  (i j : Fin p) →
  variableCovarianceAt K (fixedWindowAsVariableDimension K F) h t i j
  ≡ Fixed.covarianceAt K F h t i j
fixedCovarianceIsVariableCovariance K F h t i j = refl

fixedQuadraticIsVariableQuadratic :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : Fixed.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (h : Fixed.History F) → (t : Fixed.Time F) →
  (v : Fin p → Scalar.Scalar (Ring.orderedScalar K)) →
  variableCovarianceQuadraticAt K
    (fixedWindowAsVariableDimension K F) h t v
  ≡ Fixed.quadraticAt K F h t v
fixedQuadraticIsVariableQuadratic K F h t v = refl
