module DASHI.Physics.Closure.ShiftSeamCertificates where

open import Agda.Builtin.Nat using (Nat; _+_)
open import DASHI.Energy.ClosestPoint as CP
open import DASHI.Geometry.DefectCollapse as DC
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts; TradeoffLemma; MDLDescent; OrderedMonoid)
open import DASHI.Physics.Closure.EnergyShiftBase as ESB
open import DASHI.Physics.Closure.EnergyClosestPointShiftInstance as ECPS
open import DASHI.Physics.Closure.DefectCollapseShiftInstance as DCSI
open import DASHI.Physics.Closure.MDLDescentShiftInstance as MDSI
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.RealTernaryCarrier as RTC

-- Aggregates the empirical seam certificates for the shift stack.
-- This does not assume quadratic structure; it stays in the L1/MDL/proximal layer.
record ShiftSeams {m k : Nat} : Set₁ where
  field
    fejer : CP.FejerMonotone (ESB.EnergyShift {m} {k}) (ESB.ProjShift {m} {k})
    closest : CP.ClosestPoint (ESB.EnergyShift {m} {k}) (ESB.ProjShift {m} {k})
    defectCollapse : DC.DefectCollapse (RTC.Carrier (m + k)) Nat
    mdlDescent : ∀ x →
      MDL.OrderedMonoid._≤_ MSI.NatOrderedMonoid
        (MDL.MDLParts.MDL (MSI.MDLPartsShift {m} {k})
                          (MDL.MDLParts.T (MSI.MDLPartsShift {m} {k}) x))
        (MDL.MDLParts.MDL (MSI.MDLPartsShift {m} {k}) x)

open ShiftSeams public

shiftSeams : ∀ {m k : Nat} → ShiftSeams {m} {k}
shiftSeams {m} {k} =
  record
    { fejer = ECPS.fejerShift {m} {k}
    ; closest = ECPS.closestShift {m} {k}
    ; defectCollapse = DCSI.defectCollapseShift {m} {k}
    ; mdlDescent = MDSI.mdlyapShift {m} {k}
    }
