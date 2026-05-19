module DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibre where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (MdlLevelCoarseObservable; π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)

------------------------------------------------------------------------
-- Thin fibre over the stronger normalized package `mdlLevel × π-max`.

ShiftContractMdlLevelCoarseCarrier : Set
ShiftContractMdlLevelCoarseCarrier = ShiftContractState

π : ShiftContractMdlLevelCoarseCarrier → MdlLevelCoarseObservable
π = π-mdl-max

ShiftContractMdlLevelCoarseFibre : MdlLevelCoarseObservable → Set
ShiftContractMdlLevelCoarseFibre q = Σ ShiftContractMdlLevelCoarseCarrier (λ x → π x ≡ q)

carrier : ∀ {q} → ShiftContractMdlLevelCoarseFibre q → ShiftContractMdlLevelCoarseCarrier
carrier = fst

sound : ∀ {q} (x : ShiftContractMdlLevelCoarseFibre q) → π (carrier x) ≡ q
sound = snd
