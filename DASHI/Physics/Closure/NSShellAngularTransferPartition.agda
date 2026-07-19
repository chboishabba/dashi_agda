module DASHI.Physics.Closure.NSShellAngularTransferPartition where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra

------------------------------------------------------------------------
-- Exact finite shell/angular partition identity.
--
-- The PDE-facing construction must supply the class map and prove that its
-- total transfer equals the class sum. Once supplied, the near/tail split is
-- exact and cannot lose canonical signed cancellation before aggregation.
------------------------------------------------------------------------

nearTerm :
  (S : Scalar.ExactOrderedScalar) → {n : Nat} →
  (Fin n → Bool) →
  (Fin n → Scalar.Scalar S) →
  Fin n → Scalar.Scalar S
nearTerm S near f i with near i
... | true = f i
... | false = Scalar.zero S

tailTerm :
  (S : Scalar.ExactOrderedScalar) → {n : Nat} →
  (Fin n → Bool) →
  (Fin n → Scalar.Scalar S) →
  Fin n → Scalar.Scalar S
tailTerm S near f i with near i
... | true = Scalar.zero S
... | false = f i

pointSplitsNearTail :
  (K : Algebra.ExactOrderedCommutativeRing) → {n : Nat} →
  (near : Fin n → Bool) →
  (f : Fin n → Scalar.Scalar (Algebra.orderedScalar K)) →
  (i : Fin n) →
  f i ≡ Scalar._+_ (Algebra.orderedScalar K)
    (nearTerm (Algebra.orderedScalar K) near f i)
    (tailTerm (Algebra.orderedScalar K) near f i)
pointSplitsNearTail K near f i with near i
... | true = sym (Algebra.addZeroRight K (f i))
... | false = sym (Algebra.addZeroLeft K (f i))

sumSplitsNearTail :
  (K : Algebra.ExactOrderedCommutativeRing) → {n : Nat} →
  (near : Fin n → Bool) →
  (f : Fin n → Scalar.Scalar (Algebra.orderedScalar K)) →
  Algebra.sumFin (Algebra.orderedScalar K) f ≡
  Scalar._+_ (Algebra.orderedScalar K)
    (Algebra.sumFin (Algebra.orderedScalar K)
      (nearTerm (Algebra.orderedScalar K) near f))
    (Algebra.sumFin (Algebra.orderedScalar K)
      (tailTerm (Algebra.orderedScalar K) near f))
sumSplitsNearTail K near f =
  trans
    (Algebra.sumFinCong (Algebra.orderedScalar K)
      (pointSplitsNearTail K near f))
    (Algebra.sumFinAdd K
      (nearTerm (Algebra.orderedScalar K) near f)
      (tailTerm (Algebra.orderedScalar K) near f))

record ShellAngularTransferDecomposition
    (K : Algebra.ExactOrderedCommutativeRing) : Set₁ where
  field
    interactionClassCount : Nat
    transferByClass :
      Fin interactionClassCount →
      Scalar.Scalar (Algebra.orderedScalar K)
    nearClass : Fin interactionClassCount → Bool
    totalTransfer : Scalar.Scalar (Algebra.orderedScalar K)
    totalTransferIsClassSum :
      totalTransfer ≡
      Algebra.sumFin (Algebra.orderedScalar K) transferByClass

open ShellAngularTransferDecomposition public

totalTransferSplitsExactlyIntoNearAndTail :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (D : ShellAngularTransferDecomposition K) →
  totalTransfer D ≡
  Scalar._+_ (Algebra.orderedScalar K)
    (Algebra.sumFin (Algebra.orderedScalar K)
      (nearTerm (Algebra.orderedScalar K)
        (nearClass D) (transferByClass D)))
    (Algebra.sumFin (Algebra.orderedScalar K)
      (tailTerm (Algebra.orderedScalar K)
        (nearClass D) (transferByClass D)))
totalTransferSplitsExactlyIntoNearAndTail K D =
  trans
    (totalTransferIsClassSum D)
    (sumSplitsNearTail K (nearClass D) (transferByClass D))
