module DASHI.Physics.OrbitShellPredicate where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ

------------------------------------------------------------------------
-- Shell predicate: |Qσ(x)| = 1 (encoded as Qσ = +1 or Qσ = -1)

Shell1 : ∀ {m : Nat} → Vec IMQ.Sign m → Vec Trit m → Set
Shell1 σ x =
  (IMQ.Qσ σ x ≡ (+ 1)) ⊎ (IMQ.Qσ σ x ≡ -[1+ 0 ])

