module DASHI.Physics.SeverityGuard.Shift.Instance where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_<_)
open import Agda.Primitive using (Level; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UFTC_Lattice as UFTC using (Code; Severity)
open import DASHI.Physics.SeverityGuard.Core as SG
open import DASHI.Physics.SeverityGuardedStrict as SGS
open import DASHI.Physics.RealTernaryCarrier as RTC
open import Ultrametric as UMetric
open import DASHI.Geometry.FiberContraction as FC

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

    Uᵣ : UMetric.Ultrametric (RTC.Carrier (m + k))
    Pᵣ : RTC.Carrier (m + k) → RTC.Carrier (m + k)
    Restoreᵣ : RTC.Carrier (m + k) → RTC.Carrier (m + k)

    P-strict-on :
      ∀ {x y} →
      SG.Guard (ShiftSeverityPolicy.policyᵣ pol) x →
      SG.Guard (ShiftSeverityPolicy.policyᵣ pol) y →
      FC.FiberDistinct Pᵣ x y →
      UMetric.Ultrametric.d Uᵣ (Pᵣ x) (Pᵣ y) < UMetric.Ultrametric.d Uᵣ x y

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
    ; Uₛ = Uᵣ
    ; Pₛ = Pᵣ
    ; Restoreₛ = Restoreᵣ
    ; P-strict-onₛ = P-strict-on
    ; restore-normal-formₛ = restore-normal-form
    ; restore-idemₛ = restore-idem
    ; restore-fixesₛ = restore-fixes
    }

open ShiftSeverityGuardedStrict public
