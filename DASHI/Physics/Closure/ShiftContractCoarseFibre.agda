module DASHI.Physics.Closure.ShiftContractCoarseFibre where

open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)
open import DASHI.Physics.Closure.ShiftContractCoarseObservable as SCCO
  using (MaximalCoarseObservable; π-max)

------------------------------------------------------------------------
-- Thin fibre over the noncanonical coarse package on ShiftContractState.

ShiftContractCoarseCarrier : Set
ShiftContractCoarseCarrier = ShiftContractState

π : ShiftContractCoarseCarrier → MaximalCoarseObservable
π = π-max

ShiftContractCoarseFibre : MaximalCoarseObservable → Set
ShiftContractCoarseFibre q = Σ ShiftContractCoarseCarrier (λ x → π x ≡ q)

carrier : ∀ {q} → ShiftContractCoarseFibre q → ShiftContractCoarseCarrier
carrier = fst

sound : ∀ {q} (x : ShiftContractCoarseFibre q) → π (carrier x) ≡ q
sound = snd
