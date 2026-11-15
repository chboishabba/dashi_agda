module DASHI.Information.PNFHistoryTimeTernaryCovarianceFibreExact where

-- Native bridge: the source is a situated balanced-ternary hyperfabric
-- fibre indexed by (history,time), not an unqualified static matrix.
-- Each observation window/scale belongs to that exact source point.
-- Reuses IndexedRelationalHyperfabricSpine, canonical trits, exact
-- sample-mean/Gram covariance, and the existing finite PSD owner.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Indexed
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitGramAssembly as PSD
import DASHI.Information.PNFSampleMeanExact as Mean
import DASHI.Information.PNFCentredCovarianceExact as Centre
import DASHI.Information.PNFCovarianceQuadraticIdentityExact as Quadratic

-- Reuse the canonical indexed fabric. The situated value retains both
-- the full trit address and its dependent stalk; source identity is
-- attached at this level, not inferred from its coarse projection.
record HistoryTimeTernaryCovarianceFibre
  (K : Ring.ExactOrderedCommutativeRing)
  (depth k p : Nat) : Set₂ where
  field
    History : Set
    Time : Set
    fabric : Indexed.IndexedFabric Trit.Trit depth
    situatedAt : History → Time → Indexed.Situated fabric
    windowAt : History → Time → Mean.ActualFiniteMean K (suc (suc k)) p
    scaleAt : History → Time → Scalar.Scalar (Ring.orderedScalar K)
    scaleNonnegativeAt :
      (h : History) → (t : Time) →
      Scalar._≤_ (Ring.orderedScalar K)
        (Scalar.zero (Ring.orderedScalar K)) (scaleAt h t)
    sourceReferenceAt : History → Time → String
    consumerVersionAt : History → Time → Nat

open HistoryTimeTernaryCovarianceFibre public

ternaryAddressAt :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : HistoryTimeTernaryCovarianceFibre K depth k p) →
  (h : History F) → (t : Time F) →
  Indexed.Address Trit.Trit depth
ternaryAddressAt K F h t =
  Indexed.readAddress (fabric F) (situatedAt F h t)

covarianceAt :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : HistoryTimeTernaryCovarianceFibre K depth k p) →
  (h : History F) → (t : Time F) →
  Fin p → Fin p → Scalar.Scalar (Ring.orderedScalar K)
covarianceAt K F h t =
  Centre.scaledCovariance K
    (Mean.source (windowAt F h t)) (scaleAt F h t)

quadraticAt :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : HistoryTimeTernaryCovarianceFibre K depth k p) →
  (h : History F) → (t : Time F) →
  (Fin p → Scalar.Scalar (Ring.orderedScalar K)) →
  Scalar.Scalar (Ring.orderedScalar K)
quadraticAt K F h t =
  Quadratic.covarianceOperatorQuadratic K
    (Mean.source (windowAt F h t)) (scaleAt F h t)

covarianceAtSymmetric :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : HistoryTimeTernaryCovarianceFibre K depth k p) →
  (h : History F) → (t : Time F) →
  (i j : Fin p) →
  covarianceAt K F h t i j ≡ covarianceAt K F h t j i
covarianceAtSymmetric K F h t =
  Centre.scaledCovarianceSymmetric K
    (Mean.source (windowAt F h t)) (scaleAt F h t)

covarianceAtPSD :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : PSD.FiniteGramOrderAuthority K) →
  {depth k p : Nat} →
  (F : HistoryTimeTernaryCovarianceFibre K depth k p) →
  (h : History F) → (t : Time F) →
  (v : Fin p → Scalar.Scalar (Ring.orderedScalar K)) →
  Scalar._≤_ (Ring.orderedScalar K)
    (Scalar.zero (Ring.orderedScalar K))
    (quadraticAt K F h t v)
covarianceAtPSD K O F h t =
  Quadratic.covarianceOperatorPositiveSemidefinite K O
    (Mean.source (windowAt F h t))
    (scaleAt F h t)
    (scaleNonnegativeAt F h t)

-- An explicit same-time/same-source agreement, not inferred merely from
-- a shared ternary address. The consumer version is a separate coordinate.
record SameHistoricalWindow
  (K : Ring.ExactOrderedCommutativeRing)
  {depth k p : Nat}
  (F : HistoryTimeTernaryCovarianceFibre K depth k p)
  (h : History F) (t u : Time F) : Set₁ where
  field
    sameWindow : windowAt F h t ≡ windowAt F h u
    sameScale : scaleAt F h t ≡ scaleAt F h u
    sameAddress :
      ternaryAddressAt K F h t ≡ ternaryAddressAt K F h u
    sameConsumerVersion :
      consumerVersionAt F h t ≡ consumerVersionAt F h u

open SameHistoricalWindow public

sameHistoricalWindowPreservesCovariance :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : HistoryTimeTernaryCovarianceFibre K depth k p) →
  {h : History F} {t u : Time F} →
  SameHistoricalWindow K F h t u →
  (i j : Fin p) →
  covarianceAt K F h t i j ≡ covarianceAt K F h u i j
sameHistoricalWindowPreservesCovariance K F agreement i j
  rewrite sameWindow agreement | sameScale agreement = refl

sameHistoricalWindowPreservesQuadratic :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : HistoryTimeTernaryCovarianceFibre K depth k p) →
  {h : History F} {t u : Time F} →
  SameHistoricalWindow K F h t u →
  (v : Fin p → Scalar.Scalar (Ring.orderedScalar K)) →
  quadraticAt K F h t v ≡ quadraticAt K F h u v
sameHistoricalWindowPreservesQuadratic K F agreement v
  rewrite sameWindow agreement | sameScale agreement = refl
