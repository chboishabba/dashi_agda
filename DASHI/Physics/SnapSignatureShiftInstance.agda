module DASHI.Physics.SnapSignatureShiftInstance where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit using (⊤; tt)

open import DASHI.Physics.SnapSignature as SS
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP

-- Shift-step predicate: y is exactly Tᵣ x.
Stepᵣ : ∀ {m k : Nat} → RTC.Carrier (m + k) → RTC.Carrier (m + k) → Set
Stepᵣ {m} {k} x y = y ≡ TCP.Tᵣ {m} {k} x

-- Snap signature for shift carrier, parameterized by a tail snap threshold
-- and external chi2/MDL predicates.
record SnapSignatureShift {m k : Nat} : Set₁ where
  field
    snapThreshold : Nat
    chi2Spike : RTC.Carrier (m + k) → RTC.Carrier (m + k) → Set
    mdlDescent : RTC.Carrier (m + k) → RTC.Carrier (m + k) → Set

open SnapSignatureShift public

signature : ∀ {m k : Nat} → SnapSignatureShift {m} {k} → SS.SnapSignature {S = RTC.Carrier (m + k)}
signature {m} {k} cfg =
  record
    { step = Stepᵣ {m} {k}
    ; snapZero = λ x y →
        SS.SnapAtLeast (snapThreshold cfg)
          (TCP.tailOf m k x)
          (TCP.tailOf m k y)
    ; chi2Spike = SnapSignatureShift.chi2Spike cfg
    ; mdlDescent = SnapSignatureShift.mdlDescent cfg
    }
