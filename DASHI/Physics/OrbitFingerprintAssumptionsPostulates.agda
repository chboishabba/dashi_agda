module DASHI.Physics.OrbitFingerprintAssumptionsPostulates where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_≤_)
open import Data.Sum using (_⊎_)

open import DASHI.Physics.OrbitFingerprintAssumptions as OFA

-- Saturation seam (dimension bound), reduced to a definitional gate.
StableSignature : Nat → Nat → Nat → Set
StableSignature m _ _ = m ≡ 4

Saturation :
  ∀ {m p q : Nat} →
  StableSignature m p q →
  m ≡ 4
Saturation sig = sig
