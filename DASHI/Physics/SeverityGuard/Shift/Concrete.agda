module DASHI.Physics.SeverityGuard.Shift.Concrete where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Data.Vec using (Vec)
open import Data.Nat using (_<_ ; _≤_; z≤n; suc)

open import DASHI.Algebra.Trit using (Trit; zer)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.RealOperatorStackShift as ROSS
open import DASHI.Physics.SeverityMapping as SM
open import DASHI.Physics.MaassRestorationShift as MR using (restoreᵣ; restore-fixes; restore-idem; tailOf-restore)
open import DASHI.Physics.SeverityGuard.Shift.Wiring as W
open import DASHI.Physics.SeverityGuard.Core as SG
open import DASHI.Geometry.FiberContraction as FC
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import Ultrametric as UMetric
open import UFTC_Lattice using (Code; normal; severity)
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI

policyᵣ : ∀ {m k : Nat} → SG.SeverityPolicy (RTC.Carrier (m + k))
policyᵣ {m} {k} = record
  { code = SM.codeᵣ {m} {k}
  ; safeThreshold = SM.safeThresholdᵣ
  ; brokenThreshold = SM.brokenThresholdᵣ
  }

-- Guarded strictness for Pᵣ under severity guard.
P-strict-on :
  ∀ {m k : Nat} {x y : RTC.Carrier (m + k)} →
  SG.Guard (policyᵣ {m} {k}) x →
  SG.Guard (policyᵣ {m} {k}) y →
  FC.FiberDistinct (TCP.Pᵣ {m} {k}) x y →
  UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k})
    (TCP.Pᵣ {m} {k} x) (TCP.Pᵣ {m} {k} y)
    <
    UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) x y
P-strict-on {m} {k} {x} {y} _ _ fd =
  FC.ContractiveOnFibers.contractFiber (ROSS.strictP-fiber {m} {k}) fd

restore-normal-form'' :
  ∀ {m k : Nat} (x : RTC.Carrier (m + k)) →
  SG.Broken (policyᵣ {m} {k}) x →
  SG.Guard (policyᵣ {m} {k}) (MR.restoreᵣ {m} {k} x)
restore-normal-form'' {m} {k} x _ rewrite MR.tailOf-restore {m} {k} x | MSI.countNZ-replicate-zer {k} =
  -- Guard is severity ≤ safeThreshold; for restored state severity is 0.
  z≤n

-- reuse restoration laws from MaassRestorationShift
-- reuse restoration laws from MaassRestorationShift directly

-- Concrete wiring bundle.
shiftWiring : ∀ {m k : Nat} → W.ShiftSeverityGuardWiring {m} {k}
shiftWiring {m} {k} = record
  { policyᵣ' = policyᵣ {m} {k}
  ; Uᵣ' = FAM.ultrametricVec {n = m + k}
  ; Pᵣ' = TCP.Pᵣ {m} {k}
  ; Restoreᵣ' = MR.restoreᵣ {m} {k}
  ; P-strict-on' = P-strict-on {m} {k}
  ; restore-normal-form' = restore-normal-form'' {m} {k}
  ; restore-idem' = MR.restore-idem {m} {k}
  ; restore-fixes' = MR.restore-fixes {m} {k}
  }
