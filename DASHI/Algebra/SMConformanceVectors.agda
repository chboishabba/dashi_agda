module DASHI.Algebra.SMConformanceVectors where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.List using (List; []; _∷_)

-- Abstract state (whatever your physics state representation is)
postulate State : Set

-- Spec and impl: State → signature (finite)
postulate
  Sig : Set
  specSig : State → Sig
  implSig : State → Sig

record Vector : Set where
  constructor vec
  field input : State

Vectors : Set
Vectors = List Vector

ConformsOn : (f g : State → Sig) → Vectors → Set
ConformsOn f g [] = ⊤
ConformsOn f g (v ∷ vs) =
  (f (Vector.input v) ≡ g (Vector.input v)) × ConformsOn f g vs

-- Closure theorem you actually ship:
postulate vectors : Vectors

postulate
  physics-conformance : ConformsOn implSig specSig vectors
