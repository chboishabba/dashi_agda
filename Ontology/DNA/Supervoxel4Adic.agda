module Ontology.DNA.Supervoxel4Adic where

open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec using (Vec; []; _∷_; _++_; map)

------------------------------------------------------------------------
-- DNA-first 4-adic carrier:
-- four bases, four-way block lifts, and the first 4/16/64/256 hierarchy.

data Base : Set where
  A C G T : Base

complement : Base → Base
complement A = T
complement T = A
complement C = G
complement G = C

complement-involutive : ∀ b → complement (complement b) ≡ b
complement-involutive A = refl
complement-involutive C = refl
complement-involutive G = refl
complement-involutive T = refl

DNA4 : Set
DNA4 = Vec Base 4

DNA16 : Set
DNA16 = Vec DNA4 4

DNA64 : Set
DNA64 = Vec DNA16 4

DNA256 : Set
DNA256 = Vec DNA64 4

FlatDNA16 : Set
FlatDNA16 = Vec Base 16

FlatDNA64 : Set
FlatDNA64 = Vec Base 64

FlatDNA256 : Set
FlatDNA256 = Vec Base 256

flatten16 : DNA16 → FlatDNA16
flatten16 (a ∷ b ∷ c ∷ d ∷ []) = a ++ b ++ c ++ d

flatten64 : DNA64 → FlatDNA64
flatten64 (a ∷ b ∷ c ∷ d ∷ []) = flatten16 a ++ flatten16 b ++ flatten16 c ++ flatten16 d

flatten256 : DNA256 → FlatDNA256
flatten256 (a ∷ b ∷ c ∷ d ∷ []) = flatten64 a ++ flatten64 b ++ flatten64 c ++ flatten64 d

------------------------------------------------------------------------
-- Fixed-height 4-adic hierarchy.

record BlockLift4Adic : Set₁ where
  field
    Level1 : Set
    Level2 : Set
    Level3 : Set
    Level4 : Set

    lift12 : Level1 → Level2
    lift23 : Level2 → Level3
    lift34 : Level3 → Level4

canonicalDNA4Adic : BlockLift4Adic
canonicalDNA4Adic = record
  { Level1 = DNA4
  ; Level2 = DNA16
  ; Level3 = DNA64
  ; Level4 = DNA256
  ; lift12 = λ x → x ∷ x ∷ x ∷ x ∷ []
  ; lift23 = λ x → x ∷ x ∷ x ∷ x ∷ []
  ; lift34 = λ x → x ∷ x ∷ x ∷ x ∷ []
  }
