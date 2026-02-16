module MonsterConformance where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List     using (List; []; _∷_)
open import Data.Unit             using (⊤)
open import Data.Product          using (_×_)

open import MonsterState
open import MonsterSpec
open import MonsterVectors

------------------------------------------------------------------------
-- A foreign implementation hook (e.g., extracted from Rust evaluation).
-- You can import these as computed tables, then prove extensional equality
-- on vectors.

postulate
  implStep : State → State

------------------------------------------------------------------------
-- Conformance on vectors:

ConformsOn : (f g : State → State) → Vectors → Set
ConformsOn f g [] = ⊤
ConformsOn f g (v ∷ vs) =
  (f (Vector.input v) ≡ g (Vector.input v)) × ConformsOn f g vs

-- You’ll use: ConformsOn implStep (Spec.stepSpec spec) vectors
