module DASHI.Physics.Closure.NSShellAngularTransferPartition where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Set)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

------------------------------------------------------------------------
-- Exact finite shell/angular partition identity.
--
-- The PDE-facing construction supplies the class map and proves that total
-- transfer equals the class sum. Once supplied, the near/tail split is exact
-- and cannot lose canonical signed cancellation before aggregation.
--
-- This module carries only the additive laws required by the partition, so it
-- remains independent of the much larger physical-cutoff operator stack.
------------------------------------------------------------------------

record AdditiveTransferArithmetic : Set₁ where
  field
    Scalar : Set
    zeroScalar : Scalar
    _+_ : Scalar → Scalar → Scalar

    addZeroLeft : (a : Scalar) → _+_ zeroScalar a ≡ a
    addZeroRight : (a : Scalar) → _+_ a zeroScalar ≡ a
    addFourShuffle :
      (a b c d : Scalar) →
      _+_ (_+_ a b) (_+_ c d) ≡
      _+_ (_+_ a c) (_+_ b d)

open AdditiveTransferArithmetic public

sumFin :
  (A : AdditiveTransferArithmetic) → {n : Nat} →
  (Fin n → Scalar A) → Scalar A
sumFin A {zero} f = zeroScalar A
sumFin A {suc n} f =
  _+_ A (f zero) (sumFin A (λ i → f (suc i)))

sumFinCong :
  (A : AdditiveTransferArithmetic) → {n : Nat} →
  {f g : Fin n → Scalar A} →
  ((i : Fin n) → f i ≡ g i) →
  sumFin A f ≡ sumFin A g
sumFinCong A {zero} pointwise = refl
sumFinCong A {suc n} {f} {g} pointwise =
  cong₂ (_+_ A)
    (pointwise zero)
    (sumFinCong A (λ i → pointwise (suc i)))

sumFinAdd :
  (A : AdditiveTransferArithmetic) → {n : Nat} →
  (f g : Fin n → Scalar A) →
  sumFin A (λ i → _+_ A (f i) (g i)) ≡
  _+_ A (sumFin A f) (sumFin A g)
sumFinAdd A {zero} f g =
  sym (addZeroLeft A (zeroScalar A))
sumFinAdd A {suc n} f g =
  trans
    (cong₂ (_+_ A)
      refl
      (sumFinAdd A (λ i → f (suc i)) (λ i → g (suc i))))
    (addFourShuffle A
      (f zero)
      (g zero)
      (sumFin A (λ i → f (suc i)))
      (sumFin A (λ i → g (suc i))))

nearTerm :
  (A : AdditiveTransferArithmetic) → {n : Nat} →
  (Fin n → Bool) →
  (Fin n → Scalar A) →
  Fin n → Scalar A
nearTerm A near f i with near i
... | true = f i
... | false = zeroScalar A

tailTerm :
  (A : AdditiveTransferArithmetic) → {n : Nat} →
  (Fin n → Bool) →
  (Fin n → Scalar A) →
  Fin n → Scalar A
tailTerm A near f i with near i
... | true = zeroScalar A
... | false = f i

pointSplitsNearTail :
  (A : AdditiveTransferArithmetic) → {n : Nat} →
  (near : Fin n → Bool) →
  (f : Fin n → Scalar A) →
  (i : Fin n) →
  f i ≡ _+_ A
    (nearTerm A near f i)
    (tailTerm A near f i)
pointSplitsNearTail A near f i with near i
... | true = sym (addZeroRight A (f i))
... | false = sym (addZeroLeft A (f i))

sumSplitsNearTail :
  (A : AdditiveTransferArithmetic) → {n : Nat} →
  (near : Fin n → Bool) →
  (f : Fin n → Scalar A) →
  sumFin A f ≡
  _+_ A
    (sumFin A (nearTerm A near f))
    (sumFin A (tailTerm A near f))
sumSplitsNearTail A near f =
  trans
    (sumFinCong A (pointSplitsNearTail A near f))
    (sumFinAdd A (nearTerm A near f) (tailTerm A near f))

record ShellAngularTransferDecomposition
    (A : AdditiveTransferArithmetic) : Set₁ where
  field
    interactionClassCount : Nat
    transferByClass : Fin interactionClassCount → Scalar A
    nearClass : Fin interactionClassCount → Bool
    totalTransfer : Scalar A
    totalTransferIsClassSum :
      totalTransfer ≡ sumFin A transferByClass

open ShellAngularTransferDecomposition public

totalTransferSplitsExactlyIntoNearAndTail :
  (A : AdditiveTransferArithmetic) →
  (D : ShellAngularTransferDecomposition A) →
  totalTransfer D ≡
  _+_ A
    (sumFin A (nearTerm A (nearClass D) (transferByClass D)))
    (sumFin A (tailTerm A (nearClass D) (transferByClass D)))
totalTransferSplitsExactlyIntoNearAndTail A D =
  trans
    (totalTransferIsClassSum D)
    (sumSplitsNearTail A (nearClass D) (transferByClass D))
