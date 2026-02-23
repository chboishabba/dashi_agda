module DASHI.Physics.OrbitFingerprintAssumptions where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Orbit fingerprint seam (matches the script outputs in structure)

record OrbitFingerprint (m p q : Nat) : Set where
  field
    orbitCount : Nat
    top1       : Nat
    top2       : Nat
    top3       : Nat

------------------------------------------------------------------------
-- One distinguished sign (candidate Lorentz-like signatures)

OneDistinguished : Nat → Nat → Set
OneDistinguished p q = (p ≡ 1) ⊎ (q ≡ 1)

------------------------------------------------------------------------
-- Orbit-count minimality seam

postulate
  MinimalOrbit :
    ∀ {m p q p' q' : Nat} →
    (p + q ≡ m) →
    OneDistinguished p q →
    (fp  : OrbitFingerprint m p q) →
    (fp' : OrbitFingerprint m p' q') →
    OrbitFingerprint.orbitCount fp
      ≤ OrbitFingerprint.orbitCount fp'

------------------------------------------------------------------------
-- Saturation seam (dimension bound)

postulate
  StableSignature : Nat → Nat → Nat → Set

postulate
  Saturation :
    ∀ {m p q : Nat} →
    StableSignature m p q →
    m ≡ 4
