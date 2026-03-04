module DASHI.Algebra.SMConformanceVectors where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.List using (List; []; _∷_)

record Vector (State : Set) : Set where
  constructor vec
  field input : State

Vectors : Set → Set
Vectors State = List (Vector State)

ConformsOn : ∀ {State Sig} → (State → Sig) → (State → Sig) → Vectors State → Set
ConformsOn f g [] = ⊤
ConformsOn f g (v ∷ vs) =
  (f (Vector.input v) ≡ g (Vector.input v)) × ConformsOn f g vs

record SMConformanceAxioms : Set₁ where
  field
    State : Set
    Sig : Set
    specSig : State → Sig
    implSig : State → Sig
    vectors : Vectors State
    physics-conformance : ConformsOn implSig specSig vectors

open SMConformanceAxioms public
