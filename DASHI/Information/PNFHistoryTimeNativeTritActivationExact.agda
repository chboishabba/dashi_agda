module DASHI.Information.PNFHistoryTimeNativeTritActivationExact where

-- Every predicate activation is tied to the actual history/time-selected
-- source matrix and to the canonical BALANCED ternary carrier. No
-- generic embedding label substitutes for the exact source equality.
--
-- An optional trit encoding is a quantised observation. It is NOT
-- asserted to preserve arbitrary continuous financial-return covariance.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (Fin)
import Relation.Binary.PropositionalEquality
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import Data.Empty

import DASHI.Algebra.Trit as Trit
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFFiniteCovarianceEconomicsExact as Matrix
import DASHI.Information.PNFHistoryTimeTernaryCovarianceFibreExact as Native
import DASHI.Information.PNFSampleMeanExact as Mean
import DASHI.Information.PNFCentredCovarianceExact as Centre

private
  SOf : Ring.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Ring.orderedScalar K)

balancedTritScalar :
  (K : Ring.ExactOrderedCommutativeRing) → Trit.Trit → SOf K
balancedTritScalar K Trit.neg =
  Scalar.neg (Ring.orderedScalar K) (Scalar.one (Ring.orderedScalar K))
balancedTritScalar K Trit.zer =
  Scalar.zero (Ring.orderedScalar K)
balancedTritScalar K Trit.pos =
  Scalar.one (Ring.orderedScalar K)

balancedNegationCommutesWithScalar :
  (K : Ring.ExactOrderedCommutativeRing) →
  (t : Trit.Trit) →
  balancedTritScalar K (Trit.inv t)
  ≡ Scalar.neg (Ring.orderedScalar K) (balancedTritScalar K t)
balancedNegationCommutesWithScalar K Trit.neg =
  Relation.Binary.PropositionalEquality.sym
    (Ring.negInvolution K (Scalar.one (Ring.orderedScalar K)))
balancedNegationCommutesWithScalar K Trit.zer =
  Relation.Binary.PropositionalEquality.sym (Ring.negZero K)
balancedNegationCommutesWithScalar K Trit.pos =
  Agda.Builtin.Equality.refl

-- The same panel that supplies covariance must be proved to contain
-- the trit-coded observations at each (history,time,row,predicate).
-- Without this equality, 'ternary native' would be purely decorative.
record NativeTritActivation
  (K : Ring.ExactOrderedCommutativeRing)
  {depth k p : Nat}
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) : Set₁ where
  field
    observedTritAt :
      (h : Native.History F) → (t : Native.Time F) →
      Fin (suc (suc k)) → Fin p → Trit.Trit
    sourceIsActualTritEncoding :
      (h : Native.History F) → (t : Native.Time F) →
      (r : Fin (suc (suc k))) → (i : Fin p) →
      Matrix.entry (Centre.raw (Mean.source (Native.windowAt F h t))) r i
      ≡ balancedTritScalar K (observedTritAt h t r i)

open NativeTritActivation public

nativeTritIsSameSourceActivation :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (A : NativeTritActivation K F) →
  (h : Native.History F) → (t : Native.Time F) →
  (r : Fin (suc (suc k))) → (i : Fin p) →
  Matrix.entry (Centre.raw (Mean.source (Native.windowAt F h t))) r i
  ≡ balancedTritScalar K (observedTritAt A h t r i)
nativeTritIsSameSourceActivation K F A h t r i =
  sourceIsActualTritEncoding A h t r i

-- Exact wrong-type guard: balanced ternary SIGN is not sufficient to
-- reconstruct arbitrary original magnitudes or financial covariance.
-- This is the existing consumer non-descent theorem, not a new
-- invented notion of semantic inadequacy.
data TwoPositiveObservations : Set where
  smallPositive : TwoPositiveObservations
  largerPositive : TwoPositiveObservations

positiveSign : TwoPositiveObservations → Trit.Trit
positiveSign smallPositive = Trit.pos
positiveSign largerPositive = Trit.pos

originalMagnitude : TwoPositiveObservations → Nat
originalMagnitude smallPositive = 1
originalMagnitude largerPositive = 2

sameBalancedTritButDifferentMagnitude :
  positiveSign smallPositive ≡ positiveSign largerPositive
sameBalancedTritButDifferentMagnitude = Agda.Builtin.Equality.refl

differentOriginalMagnitude :
  originalMagnitude smallPositive ≡
  originalMagnitude largerPositive → Data.Empty.⊥
differentOriginalMagnitude ()

balancedSignMagnitudeNonDescent :
  Descent.ConsumerNonDescentWitness positiveSign originalMagnitude
balancedSignMagnitudeNonDescent =
  Descent.consumerNonDescentWitness
    smallPositive largerPositive
    sameBalancedTritButDifferentMagnitude
    differentOriginalMagnitude

balancedTritSignDoesNotRecoverOriginalMagnitude :
  Descent.FactorsThrough positiveSign originalMagnitude →
  Data.Empty.⊥
balancedTritSignDoesNotRecoverOriginalMagnitude =
  Descent.nonDescentWitnessBlocksFactorization
    balancedSignMagnitudeNonDescent
