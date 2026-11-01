module DASHI.Physics.Closure.ShiftObservableSignatureReceiptInstance where

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Nat using (_≤_)
open import Data.Product using (_,_)

import DASHI.Execution.Contract as Exec
import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
import DASHI.Physics.Closure.Basin as Basin
import DASHI.Physics.Closure.DeltaToQuadraticBridgeTheorem as DQ
import DASHI.Physics.Closure.ExecutionContract as EC
import DASHI.Physics.Closure.ExecutionContractLaws as ECL
import DASHI.Physics.Closure.ShiftContractAnchoredTrajectoryFamily as SATF
import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.Closure.Projection as Projection
import DASHI.Physics.Closure.ReceiptFromObservableSignature as RFOS

------------------------------------------------------------------------
-- Live shift execution receipts for the inhabited observable/signature path.
--
-- The execution carrier has the exact chain
--
--   start -> next -> middle -> held.
--
-- The pressure-flow carrier coarsens the last two execution steps into its
-- single next -> held step.  Keeping all three execution receipts explicit is
-- therefore necessary before any whole-chain MDL compatibility statement can
-- be made honestly.

private
  ShiftC : Exec.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

  ShiftA : Exec.Contract.ExecutionAdmissible ShiftC
  ShiftA =
    SLEI.shiftExecutionAdmissible {m = suc zero} {k = suc (suc (suc zero))}

shiftExecutionProjection :
  Projection.Projection
    (Exec.Contract.State ShiftC)
    (Exec.Contract.Source ShiftC)
    (Exec.Contract.ΔState ShiftC)
    (Exec.Contract.ΔSource ShiftC)
shiftExecutionProjection = record
  { π = Exec.Contract.π ShiftC
  ; Δ = λ x _ → Exec.Contract.Δ ShiftC x
  ; projectΔ = Exec.Contract.projectΔ ShiftC
  ; Δπ = λ s _ → Exec.Contract.projectΔ ShiftC (Exec.Contract.Δ ShiftC s)
  ; projected-delta-compatible = λ _ _ → refl
  }

shiftExecutionBasin :
  Basin.Basin (Exec.Contract.Source ShiftC)
shiftExecutionBasin = record
  { step = Exec.Contract.step ShiftC
  ; StableShell = Exec.Contract.InBasin ShiftC
  ; InBasin = Exec.Contract.InBasin ShiftC
  ; basin-eventually-stable = λ _ b → Basin.now b
  ; basin-step = Exec.Contract.ExecutionAdmissible.basin-preserved ShiftA
  }

shiftExecutionContract :
  EC.ExecutionContract
shiftExecutionContract = record
  { State = Exec.Contract.State ShiftC
  ; Source = Exec.Contract.Source ShiftC
  ; ΔState = Exec.Contract.ΔState ShiftC
  ; ΔSource = Exec.Contract.ΔSource ShiftC
  ; Eigen = Exec.Contract.Eigen ShiftC
  ; projection = shiftExecutionProjection
  ; sourceStep = Exec.Contract.step ShiftC
  ; ArrowOK = λ x y → Exec.Contract.Arrow ShiftC x ≤ Exec.Contract.Arrow ShiftC y
  ; ConeOK = λ δ → Exec.Contract.Q ShiftC δ ≤ zero
  ; mdl = Exec.Contract.L ShiftC
  ; basin = shiftExecutionBasin
  ; eigenOf = Exec.Contract.eigenOf ShiftC
  ; eigenOverlap = Exec.Contract.eigenOverlap ShiftC
  ; overlapFloor = Exec.Contract.overlapFloor ShiftC
  }

shiftReceiptStart :
  EC.State shiftExecutionContract
shiftReceiptStart = SPTI.shiftPressureStart

shiftReceiptNext :
  EC.State shiftExecutionContract
shiftReceiptNext = SPTI.shiftPressureNext

shiftReceiptMiddle :
  EC.State shiftExecutionContract
shiftReceiptMiddle = SATF.trajectoryGen STF.i2

shiftReceiptHeld :
  EC.State shiftExecutionContract
shiftReceiptHeld = SPTI.shiftPressureHeldExit

shiftReceiptStartInBasin :
  Exec.Contract.InBasin ShiftC (Exec.Contract.π ShiftC shiftReceiptStart)
shiftReceiptStartInBasin = refl

shiftReceiptNextInBasin :
  Exec.Contract.InBasin ShiftC (Exec.Contract.π ShiftC shiftReceiptNext)
shiftReceiptNextInBasin =
  Exec.Contract.ExecutionAdmissible.basin-preserved
    ShiftA
    shiftReceiptStart
    shiftReceiptStartInBasin

shiftReceiptMiddleInBasin :
  Exec.Contract.InBasin ShiftC (Exec.Contract.π ShiftC shiftReceiptMiddle)
shiftReceiptMiddleInBasin =
  Exec.Contract.ExecutionAdmissible.basin-preserved
    ShiftA
    shiftReceiptNext
    shiftReceiptNextInBasin

shiftReceiptHeldInBasin :
  Exec.Contract.InBasin ShiftC (Exec.Contract.π ShiftC shiftReceiptHeld)
shiftReceiptHeldInBasin =
  Exec.Contract.ExecutionAdmissible.basin-preserved
    ShiftA
    shiftReceiptMiddle
    shiftReceiptMiddleInBasin

shiftExecutionReceipt :
  ECL.ExecutionContractReceipt
    shiftExecutionContract
    shiftReceiptStart
    shiftReceiptNext
shiftExecutionReceipt = record
  { arrowOK = Exec.Contract.ExecutionAdmissible.arrow-monotone ShiftA shiftReceiptStart
  ; coneOK = Exec.Contract.ExecutionAdmissible.cone-delta ShiftA shiftReceiptStart
  ; mdlOK = Exec.Contract.ExecutionAdmissible.mdl-descent ShiftA shiftReceiptStart
  ; basinOK = shiftReceiptStartInBasin , shiftReceiptNextInBasin
  ; eigenOK = Exec.Contract.ExecutionAdmissible.eigen-overlap ShiftA shiftReceiptStart
  }

shiftExecutionReceiptNextMiddle :
  ECL.ExecutionContractReceipt
    shiftExecutionContract
    shiftReceiptNext
    shiftReceiptMiddle
shiftExecutionReceiptNextMiddle = record
  { arrowOK = Exec.Contract.ExecutionAdmissible.arrow-monotone ShiftA shiftReceiptNext
  ; coneOK = Exec.Contract.ExecutionAdmissible.cone-delta ShiftA shiftReceiptNext
  ; mdlOK = Exec.Contract.ExecutionAdmissible.mdl-descent ShiftA shiftReceiptNext
  ; basinOK = shiftReceiptNextInBasin , shiftReceiptMiddleInBasin
  ; eigenOK = Exec.Contract.ExecutionAdmissible.eigen-overlap ShiftA shiftReceiptNext
  }

shiftExecutionReceiptMiddleHeld :
  ECL.ExecutionContractReceipt
    shiftExecutionContract
    shiftReceiptMiddle
    shiftReceiptHeld
shiftExecutionReceiptMiddleHeld = record
  { arrowOK = Exec.Contract.ExecutionAdmissible.arrow-monotone ShiftA shiftReceiptMiddle
  ; coneOK = Exec.Contract.ExecutionAdmissible.cone-delta ShiftA shiftReceiptMiddle
  ; mdlOK = Exec.Contract.ExecutionAdmissible.mdl-descent ShiftA shiftReceiptMiddle
  ; basinOK = shiftReceiptMiddleInBasin , shiftReceiptHeldInBasin
  ; eigenOK = Exec.Contract.ExecutionAdmissible.eigen-overlap ShiftA shiftReceiptMiddle
  }

shiftReceiptPair :
  DQ.DeltaPair
shiftReceiptPair = zero , suc zero

shiftPairSupportObservableSignatureReceipt :
  RFOS.PairSupportObservableSignatureExecutionReceipt
    shiftExecutionContract
    shiftReceiptStart
    shiftReceiptNext
    SPTI.shiftObservableSignaturePressureTest
    SPTI.shiftStartPoint
    shiftReceiptPair
shiftPairSupportObservableSignatureReceipt =
  RFOS.receiptFromObservableSignatureWithPairSupport
    shiftExecutionReceipt
    SPTI.shiftStartPromotionReadyPoint
    shiftReceiptPair

shiftHeldPressureReport :
  RFOS.ObservableSignaturePressureReport
    shiftExecutionContract
    SPTI.shiftObservableSignaturePressureTest
    SPTI.shiftHeldExitPoint
shiftHeldPressureReport =
  RFOS.pressureReportFromObservableSignature
