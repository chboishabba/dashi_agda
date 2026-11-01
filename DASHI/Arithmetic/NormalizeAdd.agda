module DASHI.Arithmetic.NormalizeAdd where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Product using (_×_; _,_)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

open import DASHI.Arithmetic.NormalizeAddState using
  ( NormalizeAddState
  ; prime
  ; lhs
  ; rhs
  ; residueDepth
  ; carryDepth
  ; padicDepth
  ; carryBudget
  ; carryTrace
  ; primeProfile
  ; carryResolved
  ; normalizeAddCanonical
  )

zeroPrimeProfile = mkVec15 zero zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- First concrete carry-resolution surface.
normalizeAdd : NormalizeAddState → NormalizeAddState
normalizeAdd s =
  record s
    { residueDepth = padicDepth s
    ; carryDepth = zero
    ; carryBudget = zero
    ; carryTrace = zero
    ; primeProfile = zeroPrimeProfile
    }

normalizeAdd-primePreserved :
  ∀ s → prime (normalizeAdd s) ≡ prime s
normalizeAdd-primePreserved _ = refl

normalizeAdd-padicDepthPreserved :
  ∀ s → padicDepth (normalizeAdd s) ≡ padicDepth s
normalizeAdd-padicDepthPreserved _ = refl

normalizeAdd-residueDepthCanonical :
  ∀ s → residueDepth (normalizeAdd s) ≡ padicDepth s
normalizeAdd-residueDepthCanonical _ = refl

normalizeAdd-carryResolved :
  ∀ s → carryResolved (normalizeAdd s)
normalizeAdd-carryResolved _ = refl , refl

normalizeAdd-canonical :
  ∀ s → normalizeAddCanonical (normalizeAdd s)
normalizeAdd-canonical _ = refl , (refl , (refl , refl))
