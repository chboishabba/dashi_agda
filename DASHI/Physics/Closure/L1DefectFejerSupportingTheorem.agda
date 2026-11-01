module DASHI.Physics.Closure.L1DefectFejerSupportingTheorem where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat as Nat using (_≤_)
open import Data.Vec using (Vec)

open import DASHI.Energy.Energy as E
open import DASHI.Energy.ClosestPoint as CP
open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.Closure.EnergyShiftBase as ESB
open import DASHI.Physics.Closure.EnergyClosestPointShiftInstance as ECPS
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC

-- Supporting (non-signature) theorem:
-- the concrete shift operator is projection-like / Fejer-monotone in the
-- empirically validated L1-style defect geometry.
record L1DefectFejerSupportingTheorem {m k : Nat} : Set₁ where
  field
    -- Defect energy on masked tail coordinates.
    defectEnergy :
      RTC.Carrier (m + k) → Nat

    -- Coordinate-wise masked contraction witnesses (tail-band operators).
    shiftMaskedContractive :
      ∀ (t : Vec Trit k) →
        MSI.countNZ (TCP.shiftTail t) Nat.≤ MSI.countNZ t
    projectionMaskedContractive :
      ∀ (t : Vec Trit k) →
        MSI.countNZ (TCP.projTail t) Nat.≤ MSI.countNZ t
    defectStepMaskedContractive :
      ∀ (t : Vec Trit k) →
        MSI.countNZ (TCP.tailStep t) Nat.≤ MSI.countNZ t

    -- Lifted defect-energy descent under the actual operator Tᵣ.
    defectEnergyMonotone :
      ∀ x →
        defectEnergy (TCP.Tᵣ {m} {k} x) Nat.≤ defectEnergy x

    -- Projection-like behavior in energy geometry.
    fejerMonotone :
      CP.FejerMonotone (ESB.EnergyShift {m} {k}) (ESB.ProjShift {m} {k})
    closestPoint :
      CP.ClosestPoint (ESB.EnergyShift {m} {k}) (ESB.ProjShift {m} {k})
    projectionLikeToFix :
      ∀ x y →
        CP.FixP (ESB.ProjShift {m} {k}) y →
        E.Preorder._≤_ ESB.NatPreorder
          (E.EnergySpace.E (ESB.EnergyShift {m} {k}) x (TCP.Pᵣ {m} {k} x))
          (E.EnergySpace.E (ESB.EnergyShift {m} {k}) x y)

open L1DefectFejerSupportingTheorem public

-- Canonical supporting theorem instance for the concrete real shift stack.
l1DefectFejerSupportingTheorem :
  ∀ {m k : Nat} → L1DefectFejerSupportingTheorem {m} {k}
l1DefectFejerSupportingTheorem {m} {k} =
  let
    cp = ECPS.closestShift {m} {k}
  in
  record
    { defectEnergy = λ x → MSI.countNZ (TCP.tailOf m k x)
    ; shiftMaskedContractive = MSI.countNZ-shiftTail≤
    ; projectionMaskedContractive = MSI.countNZ-projTail≤
    ; defectStepMaskedContractive = MSI.countNZ-tailStep≤
    ; defectEnergyMonotone = MSI.resid-drop-lemma {m} {k}
    ; fejerMonotone = ECPS.fejerShift {m} {k}
    ; closestPoint = cp
    ; projectionLikeToFix = CP.ClosestPoint.closest cp
    }

-- Explicitly mark this as a precursor layer:
-- no quadratic uniqueness/signature claims here, only dynamical geometry.
record L1DefectFejerQuadraticPrecursor {m k : Nat} : Set₁ where
  field
    supportingTheorem : L1DefectFejerSupportingTheorem {m} {k}
    seamCertificates : SSC.ShiftSeams {m} {k}

l1DefectFejerQuadraticPrecursor :
  ∀ {m k : Nat} → L1DefectFejerQuadraticPrecursor {m} {k}
l1DefectFejerQuadraticPrecursor {m} {k} =
  record
    { supportingTheorem = l1DefectFejerSupportingTheorem {m} {k}
    ; seamCertificates = SSC.shiftSeams {m} {k}
    }
