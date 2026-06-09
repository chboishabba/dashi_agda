module DASHI.Physics.Closure.TailEnergyFunctional where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.RealTernaryCarrier as RTC
import DASHI.Physics.TailCollapseProof as TCP
import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI

------------------------------------------------------------------------
-- Algebraic tail-energy functional.
--
-- This is constructive algebra on the finite ternary shift carrier.  It
-- proves monotonicity for the algebraic tail-collapse step Tᵣ and collapse
-- after k tail steps.  It is not yet a Navier-Stokes flow estimate.

TailEnergy :
  ∀ {m k : Nat} →
  RTC.Carrier (m + k) →
  Nat
TailEnergy {m} {k} x =
  MSI.countNZ (TCP.tailOf m k x)

tailEnergy-step≤ :
  ∀ {m k : Nat} (x : RTC.Carrier (m + k)) →
  TailEnergy {m} {k} (TCP.Tᵣ {m} {k} x) ≤ TailEnergy {m} {k} x
tailEnergy-step≤ {m} {k} x =
  MSI.resid-drop-lemma {m} {k} x

tailEnergy-after-k-zero :
  ∀ (m k : Nat) (x : RTC.Carrier (m + k)) →
  TailEnergy {m} {k} (TCP.iterate k (TCP.Tᵣ {m} {k}) x) ≡ zero
tailEnergy-after-k-zero m k x =
  trans
    (cong MSI.countNZ (TCP.tailOf-after-Tk m k x))
    (MSI.countNZ-replicate-zer {k})

record TailEnergyFunctional (m k : Nat) : Set₁ where
  field
    carrier :
      Set

    carrierIsShiftCarrier :
      carrier ≡ RTC.Carrier (m + k)

    step :
      RTC.Carrier (m + k) → RTC.Carrier (m + k)

    stepIsTailCollapseStep :
      step ≡ TCP.Tᵣ {m} {k}

    energy :
      RTC.Carrier (m + k) → Nat

    energyIsTailCountNZ :
      ∀ x → energy x ≡ TailEnergy {m} {k} x

    stepMonotone :
      ∀ x → energy (step x) ≤ energy x

    collapsesAfterTailDepth :
      ∀ x → energy (TCP.iterate k step x) ≡ zero

open TailEnergyFunctional public

canonicalTailEnergyFunctional :
  ∀ (m k : Nat) →
  TailEnergyFunctional m k
canonicalTailEnergyFunctional m k =
  record
    { carrier =
        RTC.Carrier (m + k)
    ; carrierIsShiftCarrier =
        refl
    ; step =
        TCP.Tᵣ {m} {k}
    ; stepIsTailCollapseStep =
        refl
    ; energy =
        TailEnergy {m} {k}
    ; energyIsTailCountNZ =
        λ _ → refl
    ; stepMonotone =
        tailEnergy-step≤ {m} {k}
    ; collapsesAfterTailDepth =
        tailEnergy-after-k-zero m k
    }
