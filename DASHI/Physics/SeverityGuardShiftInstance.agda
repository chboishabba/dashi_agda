module DASHI.Physics.SeverityGuardShiftInstance where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Primitive using (Level; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UFTC_Lattice as UFTC using (Code; Severity)
open import DASHI.Physics.SeverityGuard as SG
open import DASHI.Physics.SeverityGuardedStrict as SGS
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Geometry.LCP.Stream using (lcp≥)

-- This module packages a severity-based Guard policy for the shift carrier.
-- It is parameterized over a concrete severity extractor and restore map.

record ShiftSeverityPolicy {m k : Nat} : Set₁ where
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

open ShiftSeverityPolicy public

-- Guarded strictness bundle specialized to the shift carrier, but still abstract
-- in the projection and restore maps (to avoid baking in a specific scheduler).
record ShiftSeverityGuardedStrict {m k : Nat} : Set₁ where
  field
    pol : ShiftSeverityPolicy {m} {k}

    Pᵣ : RTC.Carrier (m + k) → RTC.Carrier (m + k)
    Restoreᵣ : RTC.Carrier (m + k) → RTC.Carrier (m + k)
    projᵣ : RTC.Carrier (m + k) → (Nat → UFTC.Code)  -- supply stream view if desired
    κ : Nat

    P-strict-on :
      ∀ {x y k′} →
      SG.Guard (ShiftSeverityPolicy.policyᵣ pol) x →
      SG.Guard (ShiftSeverityPolicy.policyᵣ pol) y →
      lcp≥ (projᵣ x) (projᵣ y) k′ →
      lcp≥ (projᵣ (Pᵣ x)) (projᵣ (Pᵣ y)) (k′ + κ)

    restore-normal-form :
      ∀ x →
      SG.Broken (ShiftSeverityPolicy.policyᵣ pol) x →
      SG.Guard (ShiftSeverityPolicy.policyᵣ pol) (Restoreᵣ x)

    restore-idem :
      ∀ x → Restoreᵣ (Restoreᵣ x) ≡ Restoreᵣ x

    restore-fixes :
      ∀ x → Pᵣ (Restoreᵣ x) ≡ Restoreᵣ x

  guarded : SGS.SeverityGuardedStrict
  guarded = record
    { S = RTC.Carrier (m + k)
    ; policy = ShiftSeverityPolicy.policyᵣ pol
    ; Pₛ = Pᵣ
    ; Restoreₛ = Restoreᵣ
    ; projₛ = projᵣ
    ; κₛ = κ
    ; P-strict-onₛ = P-strict-on
    ; restore-normal-formₛ = restore-normal-form
    ; restore-idemₛ = restore-idem
    ; restore-fixesₛ = restore-fixes
    }

open ShiftSeverityGuardedStrict public
