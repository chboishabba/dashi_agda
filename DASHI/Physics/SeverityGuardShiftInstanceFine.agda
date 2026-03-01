module DASHI.Physics.SeverityGuardShiftInstanceFine where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_<_)
open import Agda.Primitive using (Level; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UFTC_Lattice as UFTC using (Code; Severity)
open import DASHI.Geometry.FiberContraction as FC
open import DASHI.Physics.SeverityGuard as SG
open import DASHI.Physics.SeverityGuardedStrictFine as SGS
open import DASHI.Physics.RealTernaryCarrier as RTC

-- Shift carrier severity policy (code + thresholds).
record ShiftSeverityPolicyFine {m k : Nat} : Set₁ where
  field
    codeᵣ : RTC.Carrier (m + k) → Code
    safeThresholdᵣ : Severity
    brokenThresholdᵣ : Severity

  policyᵣ : SG.SeverityPolicy (RTC.Carrier (m + k))
  policyᵣ = record
    { code = codeᵣ
    ; safeThreshold = safeThresholdᵣ
    ; brokenThreshold = brokenThresholdᵣ
    }

open ShiftSeverityPolicyFine public

-- Guarded strictness bundle specialized to the shift carrier using dNatFine.
record ShiftSeverityGuardedStrictFine {m k : Nat} : Set₁ where
  field
    pol : ShiftSeverityPolicyFine {m} {k}

    Pᵣ : RTC.Carrier (m + k) → RTC.Carrier (m + k)
    Restoreᵣ : RTC.Carrier (m + k) → RTC.Carrier (m + k)
    dᵣ : RTC.Carrier (m + k) → RTC.Carrier (m + k) → Nat

    P-strict-on :
      ∀ {x y} →
      SG.Guard (ShiftSeverityPolicyFine.policyᵣ pol) x →
      SG.Guard (ShiftSeverityPolicyFine.policyᵣ pol) y →
      FC.FiberDistinct Pᵣ x y →
      dᵣ (Pᵣ x) (Pᵣ y) < dᵣ x y

    restore-normal-form :
      ∀ x →
      SG.Broken (ShiftSeverityPolicyFine.policyᵣ pol) x →
      SG.Guard (ShiftSeverityPolicyFine.policyᵣ pol) (Restoreᵣ x)

    restore-idem :
      ∀ x → Restoreᵣ (Restoreᵣ x) ≡ Restoreᵣ x

    restore-fixes :
      ∀ x → Pᵣ (Restoreᵣ x) ≡ Restoreᵣ x

  guarded : SGS.SeverityGuardedStrictFine
  guarded = record
    { S = RTC.Carrier (m + k)
    ; policy = ShiftSeverityPolicyFine.policyᵣ pol
    ; Pₛ = Pᵣ
    ; Restoreₛ = Restoreᵣ
    ; dₛ = dᵣ
    ; P-strict-onₛ = P-strict-on
    ; restore-normal-formₛ = restore-normal-form
    ; restore-idemₛ = restore-idem
    ; restore-fixesₛ = restore-fixes
    }

open ShiftSeverityGuardedStrictFine public
