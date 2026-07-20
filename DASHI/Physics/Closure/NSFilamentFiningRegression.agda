module DASHI.Physics.Closure.NSFilamentFiningRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

open import Base369 using (tri-low; tri-mid; tri-high)

import DASHI.Physics.Closure.NSFilamentFiningCore as Core
import DASHI.Physics.Closure.NSFilamentFiningRuntimeBridge as Runtime

------------------------------------------------------------------------
-- Compact compile-time witnesses for the local algebra and the fail-closed
-- runtime receipt.

positiveCellSurvivesOnce :
  Core.fineCell true (Core.filamentCell tri-mid zero) ≡
  Core.filamentCell tri-mid (suc zero)
positiveCellSurvivesOnce = refl

negativeCellSurvivesOnce :
  Core.fineCell true (Core.filamentCell tri-high zero) ≡
  Core.filamentCell tri-high (suc zero)
negativeCellSurvivesOnce = refl

incoherentPositiveCellIsKilled :
  Core.fineCell false (Core.filamentCell tri-mid (suc zero)) ≡
  Core.annihilatedCell
incoherentPositiveCellIsKilled = refl

killedCellCannotReturnUnderRelaxation :
  Core.fineCellShaped true false true
    (Core.filamentCell tri-low (suc (suc zero)))
  ≡ Core.annihilatedCell
killedCellCannotReturnUnderRelaxation = refl

canonicalTrackingIsPerCell :
  Core.canonicalLifetimeTracking ≡ Core.perCell
canonicalTrackingIsPerCell = refl

runtimeParityReceiptIsClean :
  Runtime.decodedFieldParityAtPrintedPrecision
    Runtime.canonicalNSFilamentFiningRuntimeReceipt
  ≡ true
runtimeParityReceiptIsClean = refl

runtimeSweepNamesAreNotParameterEvidence :
  Runtime.threeNamedRunsActuallyParameterised
    Runtime.canonicalNSFilamentFiningRuntimeReceipt
  ≡ false
runtimeSweepNamesAreNotParameterEvidence = refl

runtimePhysicalBridgeRemainsOpen :
  Runtime.codecToNSPhysicalBridgeProved
    Runtime.canonicalNSFilamentFiningRuntimeReceipt
  ≡ false
runtimePhysicalBridgeRemainsOpen = refl
