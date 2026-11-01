module DASHI.Physics.YangMills.BalabanSU2CMP98Remainder where

open import Agda.Builtin.Equality using (_≡_)

record CMP98Remainder (Input Output Size : Set) : Set₁ where
  field
    full main remainder : Input → Output
    combine : Output → Output → Output
    exactDecomposition : ∀ input → full input ≡ combine (main input) (remainder input)

    remainderSize inputSize : Input → Size
    LessEqual : Size → Size → Set
    analyticBound : ∀ input → LessEqual (remainderSize input) (inputSize input)

open CMP98Remainder public
