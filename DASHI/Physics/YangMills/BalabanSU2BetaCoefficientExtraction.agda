module DASHI.Physics.YangMills.BalabanSU2BetaCoefficientExtraction where

open import Agda.Builtin.Equality using (_≡_)

record BetaCoefficientExtraction (Direction Scalar : Set) : Set₁ where
  field
    polarization yangMillsTensor remainder : Direction → Direction → Scalar
    beta : Scalar
    scale : Scalar → Scalar → Scalar
    add : Scalar → Scalar → Scalar
    decomposition :
      ∀ left right →
      polarization left right
        ≡ add (scale beta (yangMillsTensor left right)) (remainder left right)
    betaUnique :
      ∀ candidate →
      (∀ left right →
        polarization left right
          ≡ add (scale candidate (yangMillsTensor left right)) (remainder left right)) →
      candidate ≡ beta

open BetaCoefficientExtraction public
