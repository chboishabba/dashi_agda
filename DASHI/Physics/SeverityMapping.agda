module DASHI.Physics.SeverityMapping where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_⊓_; _≤_)
open import Data.Vec using (Vec)
open import DASHI.Algebra.Trit using (Trit; zer)
open import UFTC_Lattice using (Code; Severity; normal; special)

open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI using (countNZ)

-- Clamp severity into 0..9 using min (⊓).
clamp9 : Nat → Nat
clamp9 n = n ⊓ 9

-- Severity mapping: use tail nonzero count as defect magnitude.
codeᵣ : ∀ {m k : Nat} → RTC.Carrier (m + k) → Code
codeᵣ {m} {k} x with countNZ (TCP.tailOf m k x)
... | zero    = normal 0
... | suc n   = special (clamp9 (suc n))

-- Policy thresholds (configurable).
safeThresholdᵣ : Severity
safeThresholdᵣ = 3

brokenThresholdᵣ : Severity
brokenThresholdᵣ = 4
