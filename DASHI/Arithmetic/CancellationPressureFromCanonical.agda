module DASHI.Arithmetic.CancellationPressureFromCanonical where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; z≤n)
open import Data.Nat.Properties as NatP using (≤-refl)

open import DASHI.Arithmetic.NormalizeAdd using
  ( normalizeAdd
  ; normalizeAdd-canonical
  )
open import DASHI.Arithmetic.NormalizeAddState using
  ( NormalizeAddState
  ; carryBudget
  ; padicDepth
  ; normalizeAddCanonical
  )
open import DASHI.Arithmetic.CancellationPressureCore
open import DASHI.Arithmetic.CancellationPressureBound
open import DASHI.Arithmetic.CanonicalResidueZero using
  ( canonicalResidueBudget-fromCanonical
  )

-- Cheapest honest state-side semantics supported by the current model:
-- cancellation pressure is the current carry-budget proxy, and support
-- pressure is the p-adic depth budget available to absorb it.

StateCancellationPressure : NormalizeAddState → Nat
StateCancellationPressure = carryBudget

StateSupportPressure : NormalizeAddState → Nat
StateSupportPressure = padicDepth

canonicalCancellationPressure : NormalizeAddState → Nat
canonicalCancellationPressure = StateCancellationPressure

canonicalCancellationPressureBoundFn : NormalizeAddState → Nat
canonicalCancellationPressureBoundFn = StateCancellationPressure

canonicalCancellationPressure≤bound :
  ∀ s → canonicalCancellationPressure s ≤ canonicalCancellationPressureBoundFn s
canonicalCancellationPressure≤bound _ = NatP.≤-refl

canonicalCancellationPressure-step :
  ∀ s → canonicalCancellationPressure (normalizeAdd s) ≤ canonicalCancellationPressure s
canonicalCancellationPressure-step _ = z≤n

canonicalCancellationPressureBound-step :
  ∀ s →
  canonicalCancellationPressureBoundFn (normalizeAdd s) ≤
  canonicalCancellationPressureBoundFn s
canonicalCancellationPressureBound-step _ = z≤n

canonicalCancellationPressureCore : CancellationPressureCore
canonicalCancellationPressureCore =
  record
    { Carrier = NormalizeAddState
    ; step = normalizeAdd
    ; cancellationPressure = canonicalCancellationPressure
    ; pressure-step = canonicalCancellationPressure-step
    }

canonicalCancellationPressureBound : CancellationPressureBound canonicalCancellationPressureCore
canonicalCancellationPressureBound =
  record
    { pressureBound = canonicalCancellationPressureBoundFn
    ; pressure≤bound = canonicalCancellationPressure≤bound
    ; bound-step = canonicalCancellationPressureBound-step
    }

record CancellationPressureFromCanonical : Set₁ where
  field
    core : CancellationPressureCore
    bound : CancellationPressureBound core
    canonicalPressureBound :
      ∀ s →
      normalizeAddCanonical s →
      canonicalCancellationPressure s ≤ canonicalCancellationPressureBoundFn s
    normalizeAddOneStepCanonical :
      ∀ s → normalizeAddCanonical (normalizeAdd s)
    normalizeAddOneStepBound :
      ∀ s →
      canonicalCancellationPressure (normalizeAdd s) ≤
      canonicalCancellationPressureBoundFn (normalizeAdd s)

canonicalCancellationPressureFromCanonical : CancellationPressureFromCanonical
canonicalCancellationPressureFromCanonical =
  record
    { core = canonicalCancellationPressureCore
    ; bound = canonicalCancellationPressureBound
    ; canonicalPressureBound = λ _ _ → NatP.≤-refl
    ; normalizeAddOneStepCanonical = normalizeAdd-canonical
    ; normalizeAddOneStepBound = λ _ → NatP.≤-refl
    }

canonicalPressureBounded :
  ∀ s →
  normalizeAddCanonical s →
  canonicalCancellationPressure s ≤ canonicalCancellationPressureBoundFn s
canonicalPressureBounded _ _ = NatP.≤-refl

canonical⇒boundedPressure :
  ∀ s →
  normalizeAddCanonical s →
  StateCancellationPressure s ≤ StateSupportPressure s
canonical⇒boundedPressure s canon
  rewrite canonicalResidueBudget-fromCanonical s canon
  = z≤n

normalizeAddOneStepCanonical :
  ∀ s → normalizeAddCanonical (normalizeAdd s)
normalizeAddOneStepCanonical = normalizeAdd-canonical

normalizeAddOneStepBound :
  ∀ s →
  canonicalCancellationPressure (normalizeAdd s) ≤
  canonicalCancellationPressureBoundFn (normalizeAdd s)
normalizeAddOneStepBound _ = NatP.≤-refl

normalizeAddOneStepSupportBound :
  ∀ s →
  StateCancellationPressure (normalizeAdd s) ≤
  StateSupportPressure (normalizeAdd s)
normalizeAddOneStepSupportBound s =
  canonical⇒boundedPressure (normalizeAdd s) (normalizeAdd-canonical s)
