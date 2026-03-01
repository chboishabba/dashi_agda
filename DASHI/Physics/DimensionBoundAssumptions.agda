module DASHI.Physics.DimensionBoundAssumptions where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; suc; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (_≤_; _<_)
open import Data.Vec using (Vec)

open import DASHI.Physics.RealTernaryCarrier as RTC

------------------------------------------------------------------------
-- Indefinite signature interface

record IndefiniteSignature {A : Set} (B : A → A → Nat) : Set₁ where
  field
    Q     : A → Nat
    Q-def : ∀ x → Q x ≡ B x x
    sig   : Nat × Nat

------------------------------------------------------------------------
-- Orbit profile seam for the |Q|=1 shell

record ShellOrbitProfile (m : Nat) : Set where
  field
    orbitCount : Nat
    top1       : Nat
    top2       : Nat
    top3       : Nat

------------------------------------------------------------------------
-- Minimal dimension-bound gate wrapper (assumption seam)

record DimensionBoundGate : Set₁ where
  field
    hasBound : Set

------------------------------------------------------------------------
-- Dimension-bound theorem seam (moved to DimensionBoundAssumptionsPostulates)
