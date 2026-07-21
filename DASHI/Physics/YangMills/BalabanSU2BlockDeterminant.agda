module DASHI.Physics.YangMills.BalabanSU2BlockDeterminant where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ)

open import DASHI.Physics.YangMills.BalabanBlockDeterminantProduct using
  (shellProduct; blockDeterminantProductFromStep;
   intervalProduct; blockDeterminantIntervalFromStep)

record FiniteBlockDeterminantData (Scalar : Set) : Set₁ where
  field
    one : Scalar
    multiply : Scalar → Scalar → Scalar
    determinant : ℕ → Scalar
    conditionalDeterminant : ℕ → Scalar

    multiplyAssociative :
      ∀ a b c →
      multiply (multiply a b) c ≡ multiply a (multiply b c)

    multiplyRightIdentity :
      ∀ a → multiply a one ≡ a

    determinantBase : determinant 0 ≡ one

    blockCholeskyStep :
      ∀ n →
      determinant (Data.Nat.Base.suc n)
        ≡ multiply (determinant n) (conditionalDeterminant n)

open FiniteBlockDeterminantData public

finiteBlockCholeskyProduct :
  ∀ {Scalar}
  (detData : FiniteBlockDeterminantData Scalar) →
  ∀ n →
  determinant detData n
    ≡ shellProduct (one detData) (multiply detData)
        (conditionalDeterminant detData) n
finiteBlockCholeskyProduct detData =
  blockDeterminantProductFromStep
    (one detData) (multiply detData)
    (determinant detData) (conditionalDeterminant detData)
    (determinantBase detData) (blockCholeskyStep detData)

finiteBlockCholeskyInterval :
  ∀ {Scalar}
  (detData : FiniteBlockDeterminantData Scalar) →
  ∀ k n →
  determinant detData (Data.Nat.Base._+_ n k)
  ≡ multiply detData (determinant detData k)
      (intervalProduct (one detData) (multiply detData)
        (conditionalDeterminant detData) k n)
finiteBlockCholeskyInterval detData =
  blockDeterminantIntervalFromStep
    (one detData) (multiply detData)
    (determinant detData) (conditionalDeterminant detData)
    (multiplyAssociative detData) (multiplyRightIdentity detData)
    (blockCholeskyStep detData)
