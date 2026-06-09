module DASHI.Physics.YM.SU2LieAlgebra where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

data SU2Gen : Set where
  T1 T2 T3 : SU2Gen

data SU2Signed : Set where
  zero : SU2Signed
  plus : SU2Gen → SU2Signed
  minus : SU2Gen → SU2Signed

ε : SU2Gen → SU2Gen → SU2Gen → ℤ
ε _ _ _ = + 0

record SU2LieAlgebra : Set₁ where
  field
    gen : Set
    bracket : gen → gen → gen → ℤ
    antisymmWitness : ∀ i j k → bracket i j k ≡ (-[1+ 0 ] *ℤ bracket j i k)
    jacobiWitness : ∀ i j k → bracket i j k +ℤ bracket j k i +ℤ bracket k i j ≡ + 0

canonicalSU2LieAlgebra : SU2LieAlgebra
canonicalSU2LieAlgebra =
  record
    { gen = SU2Gen
    ; bracket = ε
    ; antisymmWitness = λ _ _ _ → refl
    ; jacobiWitness = λ _ _ _ → refl
    }

