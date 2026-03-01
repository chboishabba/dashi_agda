module DASHI.Physics.OrbitFingerprintAssumptionsPostulates where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_≤_)
open import Data.Sum using (_⊎_)

open import DASHI.Physics.OrbitFingerprintAssumptions as OFA

-- Orbit-count minimality seam (assumption module).
postulate
  MinimalOrbit :
    ∀ {m p q p' q' : Nat} →
    (p + q ≡ m) →
    OFA.OneDistinguished p q →
    (fp  : OFA.OrbitFingerprint m p q) →
    (fp' : OFA.OrbitFingerprint m p' q') →
    OFA.OrbitFingerprint.orbitCount fp
      ≤ OFA.OrbitFingerprint.orbitCount fp'

-- Saturation seam (dimension bound) (assumption module).
postulate
  StableSignature : Nat → Nat → Nat → Set

  Saturation :
    ∀ {m p q : Nat} →
    StableSignature m p q →
    m ≡ 4
