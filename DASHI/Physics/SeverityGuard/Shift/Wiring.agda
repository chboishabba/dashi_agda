module DASHI.Physics.SeverityGuard.Shift.Wiring where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_<_)
open import Agda.Primitive using (Level; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UFTC_Lattice as UFTC using (Code; Severity)
open import Ultrametric as UMetric
open import DASHI.Geometry.FiberContraction as FC
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.SeverityGuard.Shift.Instance as SGSI
open import DASHI.Physics.SeverityGuard.Core as SG

-- Concrete wiring target for the shift carrier:
-- Guard/Snap/Broken are driven by UFTC_Lattice.Code severity.
-- P is deterministic (Pᵣ), conditionality is enforced by Guard.
record ShiftSeverityGuardWiring {m k : Nat} : Set₁ where
  field
    -- Severity policy for each state
    policyᵣ' : SG.SeverityPolicy (RTC.Carrier (m + k))

    Uᵣ' : UMetric.Ultrametric (RTC.Carrier (m + k))

    -- Deterministic tail-kill projection and restoration
    Pᵣ' : RTC.Carrier (m + k) → RTC.Carrier (m + k)
    Restoreᵣ' : RTC.Carrier (m + k) → RTC.Carrier (m + k)

    -- Guarded strictness of P under severity guard
    P-strict-on' :
      ∀ {x y} →
      SG.Guard policyᵣ' x →
      SG.Guard policyᵣ' y →
      FC.FiberDistinct Pᵣ' x y →
      UMetric.Ultrametric.d Uᵣ' (Pᵣ' x) (Pᵣ' y) < UMetric.Ultrametric.d Uᵣ' x y

    restore-normal-form' :
      ∀ x →
      SG.Broken policyᵣ' x →
      SG.Guard policyᵣ' (Restoreᵣ' x)

    restore-idem' :
      ∀ x → Restoreᵣ' (Restoreᵣ' x) ≡ Restoreᵣ' x

    restore-fixes' :
      ∀ x → Pᵣ' (Restoreᵣ' x) ≡ Restoreᵣ' x

  shiftStrict : SGSI.ShiftSeverityGuardedStrict {m} {k}
  shiftStrict =
    record
      { pol = record
          { codeᵣ = SG.SeverityPolicy.code policyᵣ'
          ; safeThresholdᵣ = SG.SeverityPolicy.safeThreshold policyᵣ'
          ; brokenThresholdᵣ = SG.SeverityPolicy.brokenThreshold policyᵣ'
          }
      ; Uᵣ = Uᵣ'
      ; Pᵣ = Pᵣ'
      ; Restoreᵣ = Restoreᵣ'
    ; P-strict-on = P-strict-on'
    ; restore-normal-form = restore-normal-form'
    ; restore-idem = restore-idem'
    ; restore-fixes = restore-fixes'
    }

open ShiftSeverityGuardWiring public
