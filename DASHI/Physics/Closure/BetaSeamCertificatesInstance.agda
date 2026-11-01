module DASHI.Physics.Closure.BetaSeamCertificatesInstance where

open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.Closure.EnergyShiftBase as ESB
open import DASHI.Physics.Closure.EnergyClosestPointShiftInstance as ECPS
open import DASHI.Physics.Closure.DefectCollapseShiftInstance as DCSI
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.MDLDescentShiftInstance as MDSI
open import DASHI.Physics.Closure.BetaSeamCertificates as BSC
open import DASHI.MDL.MDLDescentTradeoff as MDL

-- Concrete beta-space seam pack for the shift instance.
-- Uses the same carrier/projection/energy as the shift closure plumbing.
betaSeamsShift : ∀ {m k : Nat} →
  BSC.BetaSeams
    (ESB.EnergyShift {m} {k})
    (ESB.ProjShift {m} {k})
    Nat
    (MSI.MDLPartsShift {m} {k})
    (MSI.TradeoffShift {m} {k})
betaSeamsShift {m} {k} =
  record
    { fejer = ECPS.fejerShift {m} {k}
    ; closest = ECPS.closestShift {m} {k}
    ; defectCollapse = DCSI.defectCollapseShift {m} {k}
    ; mdlDescent = MDSI.mdlyapShift {m} {k}
    }
