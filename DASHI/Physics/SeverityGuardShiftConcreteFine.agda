module DASHI.Physics.SeverityGuardShiftConcreteFine where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_≤_; z≤n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Geometry.FiberContraction as FC
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Physics.RealOperatorStackShift as ROSS
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.SeverityMapping as SM
open import DASHI.Physics.SeverityGuard as SG
open import DASHI.Physics.SeverityGuardShiftWiringFine as W
open import DASHI.Physics.MaassRestorationShift as MR using (restoreᵣ; restore-idem; restore-fixes; tailOf-restore)
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI

-- Concrete severity policy for shift carrier.
policyᵣ : ∀ {m k : Nat} → SG.SeverityPolicy (RTC.Carrier (m + k))
policyᵣ {m} {k} = record
  { code = SM.codeᵣ {m} {k}
  ; safeThreshold = SM.safeThresholdᵣ
  ; brokenThreshold = SM.brokenThresholdᵣ
  }

-- Strictness in dNatFine: if two states are distinct but in the same fiber, Pᵣ is strictly contractive.
P-strict-on :
  ∀ {m k : Nat} {x y : RTC.Carrier (m + k)} →
  SG.Guard (policyᵣ {m} {k}) x →
  SG.Guard (policyᵣ {m} {k}) y →
  FC.FiberDistinct (TCP.Pᵣ {m} {k}) x y →
  FAM.dNatFine (TCP.Pᵣ {m} {k} x) (TCP.Pᵣ {m} {k} y) < FAM.dNatFine x y
P-strict-on {m} {k} _ _ fd =
  FC.ContractiveOnFibers.contractFiber (ROSS.strictP-fiber {m} {k}) fd

restore-normal-form'' :
  ∀ {m k : Nat} (x : RTC.Carrier (m + k)) →
  SG.Broken (policyᵣ {m} {k}) x →
  SG.Guard (policyᵣ {m} {k}) (MR.restoreᵣ {m} {k} x)
restore-normal-form'' {m} {k} x _ rewrite MR.tailOf-restore {m} {k} x | MSI.countNZ-replicate-zer {k} =
  z≤n

-- Concrete wiring bundle using FineAgreement strictness.
shiftWiringFine : ∀ {m k : Nat} → W.ShiftSeverityGuardWiringFine {m} {k}
shiftWiringFine {m} {k} = record
  { policyᵣ' = policyᵣ {m} {k}
  ; Pᵣ' = TCP.Pᵣ {m} {k}
  ; Restoreᵣ' = MR.restoreᵣ {m} {k}
  ; dᵣ' = FAM.dNatFine
  ; P-strict-on' = P-strict-on {m} {k}
  ; restore-normal-form' = restore-normal-form'' {m} {k}
  ; restore-idem' = MR.restore-idem {m} {k}
  ; restore-fixes' = MR.restore-fixes {m} {k}
  }
