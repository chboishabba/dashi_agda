module DASHI.Physics.SeverityGuardShiftWiring where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Primitive using (Level; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UFTC_Lattice as UFTC using (Code; Severity)
open import DASHI.Geometry.LCP.Stream using (Stream; lcp≥)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.SeverityGuardShiftInstance as SGSI
open import DASHI.Physics.SeverityGuard as SG

-- Concrete wiring target for the shift carrier:
-- Guard/Snap/Broken are driven by UFTC_Lattice.Code severity.
-- P is deterministic (Pᵣ), conditionality is enforced by Guard.
record ShiftSeverityGuardWiring {m k : Nat} : Set₁ where
  field
    -- Severity policy for each state
    policyᵣ' : SG.SeverityPolicy (RTC.Carrier (m + k))

    -- Deterministic tail-kill projection and restoration
    Pᵣ' : RTC.Carrier (m + k) → RTC.Carrier (m + k)
    Restoreᵣ' : RTC.Carrier (m + k) → RTC.Carrier (m + k)

    -- Stream view for LCP depth reasoning
    projᵣ' : RTC.Carrier (m + k) → Stream Code

    -- Strictness gain
    κ' : Nat

    -- Guarded strictness of P under severity guard
    P-strict-on' :
      ∀ {x y k′} →
      SG.Guard policyᵣ' x →
      SG.Guard policyᵣ' y →
      lcp≥ (projᵣ' x) (projᵣ' y) k′ →
      lcp≥ (projᵣ' (Pᵣ' x)) (projᵣ' (Pᵣ' y)) (k′ + κ')

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
      ; Pᵣ = Pᵣ'
      ; Restoreᵣ = Restoreᵣ'
      ; projᵣ = projᵣ'
      ; κ = κ'
    ; P-strict-on = P-strict-on'
    ; restore-normal-form = restore-normal-form'
    ; restore-idem = restore-idem'
    ; restore-fixes = restore-fixes'
    }

open ShiftSeverityGuardWiring public
