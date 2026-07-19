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
  (data : FiniteBlockDeterminantData Scalar) →
  ∀ n →
  determinant data n
    ≡ shellProduct (one data) (multiply data)
        (conditionalDeterminant data) n
finiteBlockCholeskyProduct data =
  blockDeterminantProductFromStep
    (one data) (multiply data)
    (determinant data) (conditionalDeterminant data)
    (determinantBase data) (blockCholeskyStep data)

finiteBlockCholeskyInterval :
  ∀ {Scalar}
  (data : FiniteBlockDeterminantData Scalar) →
  ∀ k n →
  determinant data (Data.Nat.Base._+_ n k)
  ≡ multiply data (determinant data k)
      (intervalProduct (one data) (multiply data)
        (conditionalDeterminant data) k n)
finiteBlockCholeskyInterval data =
  blockDeterminantIntervalFromStep
    (one data) (multiply data)
    (determinant data) (conditionalDeterminant data)
    (multiplyAssociative data) (multiplyRightIdentity data)
    (blockCholeskyStep data)
