module DASHI.Physics.MaskedCone where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Data.Vec using (Vec; []; _∷_)
open import Data.Integer using (ℤ; +_; -[1+_])

open import DASHI.Algebra.Trit using (Trit; zer; pos)
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.SignatureFromMask as SFM

------------------------------------------------------------------------
-- Cone classification induced by a masked quadratic.
--
-- Integer order is kept as an explicit assumption seam so this module does
-- not depend on stdlib-version-specific order constructor names.

postulate
  _<ℤ_ : ℤ → ℤ → Set

Negative :
  ∀ {m : Nat} → Vec IMQ.Sign m → Vec Trit m → Set
Negative σ x = IMQ.Qσ σ x <ℤ + 0

Null :
  ∀ {m : Nat} → Vec IMQ.Sign m → Vec Trit m → Set
Null σ x = IMQ.Qσ σ x ≡ + 0

Positive :
  ∀ {m : Nat} → Vec IMQ.Sign m → Vec Trit m → Set
Positive σ x = + 0 <ℤ IMQ.Qσ σ x

Orthogonal :
  ∀ {m : Nat} → Vec IMQ.Sign m → Vec Trit m → Vec Trit m → Set
Orthogonal σ x y = IMQ.B2σ σ x y ≡ + 0

------------------------------------------------------------------------
-- The fixed physical profile is a concrete instance of the parameterized
-- mask algebra, not a replacement for it.

lorentzMask : Vec IMQ.Sign 4
lorentzMask =
  IMQ.minus ∷ IMQ.plus ∷ IMQ.plus ∷ IMQ.plus ∷ []

lorentzSignature : SFM.signature lorentzMask ≡ (1 , 3)
lorentzSignature = refl

neutral4 : Vec Trit 4
neutral4 = zer ∷ zer ∷ zer ∷ zer ∷ []

timeAxis : Vec Trit 4
timeAxis = pos ∷ zer ∷ zer ∷ zer ∷ []

spaceAxis₁ : Vec Trit 4
spaceAxis₁ = zer ∷ pos ∷ zer ∷ zer ∷ []

spaceAxis₂ : Vec Trit 4
spaceAxis₂ = zer ∷ zer ∷ pos ∷ zer ∷ []

spaceAxis₃ : Vec Trit 4
spaceAxis₃ = zer ∷ zer ∷ zer ∷ pos ∷ []

neutral-null : Null lorentzMask neutral4
neutral-null = refl

Q-timeAxis : IMQ.Qσ lorentzMask timeAxis ≡ -[1+ 0 ]
Q-timeAxis = refl

Q-spaceAxis₁ : IMQ.Qσ lorentzMask spaceAxis₁ ≡ + 1
Q-spaceAxis₁ = refl

Q-spaceAxis₂ : IMQ.Qσ lorentzMask spaceAxis₂ ≡ + 1
Q-spaceAxis₂ = refl

Q-spaceAxis₃ : IMQ.Qσ lorentzMask spaceAxis₃ ≡ + 1
Q-spaceAxis₃ = refl

------------------------------------------------------------------------
-- Coordinate axes are pairwise orthogonal for the diagonal mask.

time⊥space₁ : Orthogonal lorentzMask timeAxis spaceAxis₁
time⊥space₁ = refl

time⊥space₂ : Orthogonal lorentzMask timeAxis spaceAxis₂
time⊥space₂ = refl

time⊥space₃ : Orthogonal lorentzMask timeAxis spaceAxis₃
time⊥space₃ = refl

space₁⊥space₂ : Orthogonal lorentzMask spaceAxis₁ spaceAxis₂
space₁⊥space₂ = refl

space₁⊥space₃ : Orthogonal lorentzMask spaceAxis₁ spaceAxis₃
space₁⊥space₃ = refl

space₂⊥space₃ : Orthogonal lorentzMask spaceAxis₂ spaceAxis₃
space₂⊥space₃ = refl

------------------------------------------------------------------------
-- A compact witness that the fixed profile is genuinely indefinite.

record IndefiniteWitness {m : Nat} (σ : Vec IMQ.Sign m) : Set where
  field
    negativeVector : Vec Trit m
    positiveVector : Vec Trit m
    negativeValue  : Negative σ negativeVector
    positiveValue  : Positive σ positiveVector

postulate
  minusOne<zero : -[1+ 0 ] <ℤ + 0
  zero<plusOne : + 0 <ℤ + 1

lorentzIndefinite : IndefiniteWitness lorentzMask
lorentzIndefinite =
  record
    { negativeVector = timeAxis
    ; positiveVector = spaceAxis₁
    ; negativeValue = minusOne<zero
    ; positiveValue = zero<plusOne
    }
