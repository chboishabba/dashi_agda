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
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.Closure.Projection as Projection
import DASHI.Physics.Closure.ReceiptFromObservableSignature as RFOS

------------------------------------------------------------------------
-- Live shift execution receipt for the inhabited observable/signature path.
--
-- This replaces the identity-step receipt surface with one concrete live
-- shift step from the existing anchored trajectory.  The observable/signature
-- promotion point now lives on the same non-singleton shift pressure carrier.

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

shiftReceiptStartInBasin :
  Exec.Contract.InBasin ShiftC (Exec.Contract.π ShiftC shiftReceiptStart)
shiftReceiptStartInBasin = refl

shiftExecutionReceipt :
  ECL.ExecutionContractReceipt
    shiftExecutionContract
    shiftReceiptStart
    shiftReceiptNext
shiftExecutionReceipt = record
  { arrowOK = Exec.Contract.ExecutionAdmissible.arrow-monotone ShiftA shiftReceiptStart
  ; coneOK = Exec.Contract.ExecutionAdmissible.cone-delta ShiftA shiftReceiptStart
  ; mdlOK = Exec.Contract.ExecutionAdmissible.mdl-descent ShiftA shiftReceiptStart
  ; basinOK =
      shiftReceiptStartInBasin
      ,
      Exec.Contract.ExecutionAdmissible.basin-preserved
        ShiftA
        shiftReceiptStart
        shiftReceiptStartInBasin
  ; eigenOK = Exec.Contract.ExecutionAdmissible.eigen-overlap ShiftA shiftReceiptStart
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
