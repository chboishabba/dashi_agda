module DASHI.Physics.Closure.MDLLyapunovCompatibility where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (z≤n)
open import MDL.Core.Core as OldMDL

open import DASHI.Execution.Contract as Exec
open import DASHI.Physics.Closure.ExecutionContract as EC
open import DASHI.Physics.Closure.ExecutionContractLaws as ECL
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL
open import DASHI.Physics.Closure.ShiftObservableSignatureReceiptInstance as SRI

-- Compatibility-only generic Lyapunov witness for older interfaces that still
-- quantify over arbitrary transition systems.
--
-- The theorem-facing surfaces below expose the complete live execution chain.
abstract
  mdlLyapTrivial : ∀ {S : Set} (T : S → S) → OldMDL.Lyapunov T
  mdlLyapTrivial T =
    record
      { L = λ _ → zero
      ; descent = λ _ → z≤n
      }

private
  shiftSourceLyapunov :
    OldMDL.Lyapunov (EC.sourceStep SRI.shiftExecutionContract)
  shiftSourceLyapunov =
    MDLL.lyapunovShift
      {m = suc zero}
      {k = suc (suc (suc zero))}

currentShiftLyapunovReceipt :
  ECL.ExecutionContractLyapunovReceipt
    SRI.shiftExecutionContract
    SRI.shiftReceiptStart
    SRI.shiftReceiptNext
currentShiftLyapunovReceipt = record
  { sourceLyapunov = shiftSourceLyapunov
  ; receipt = SRI.shiftExecutionReceipt
  }

currentShiftLyapunovReceiptNextMiddle :
  ECL.ExecutionContractLyapunovReceipt
    SRI.shiftExecutionContract
    SRI.shiftReceiptNext
    SRI.shiftReceiptMiddle
currentShiftLyapunovReceiptNextMiddle = record
  { sourceLyapunov = shiftSourceLyapunov
  ; receipt = SRI.shiftExecutionReceiptNextMiddle
  }

currentShiftLyapunovReceiptMiddleHeld :
  ECL.ExecutionContractLyapunovReceipt
    SRI.shiftExecutionContract
    SRI.shiftReceiptMiddle
    SRI.shiftReceiptHeld
currentShiftLyapunovReceiptMiddleHeld = record
  { sourceLyapunov = shiftSourceLyapunov
  ; receipt = SRI.shiftExecutionReceiptMiddleHeld
  }

currentShiftLyapunovAdmissible :
  EC.AdmissibleStep
    SRI.shiftExecutionContract
    SRI.shiftReceiptStart
    SRI.shiftReceiptNext
currentShiftLyapunovAdmissible =
  ECL.bridge→admissible currentShiftLyapunovReceipt

currentShiftLyapunovAdmissibleNextMiddle :
  EC.AdmissibleStep
    SRI.shiftExecutionContract
    SRI.shiftReceiptNext
    SRI.shiftReceiptMiddle
currentShiftLyapunovAdmissibleNextMiddle =
  ECL.bridge→admissible currentShiftLyapunovReceiptNextMiddle

currentShiftLyapunovAdmissibleMiddleHeld :
  EC.AdmissibleStep
    SRI.shiftExecutionContract
    SRI.shiftReceiptMiddle
    SRI.shiftReceiptHeld
currentShiftLyapunovAdmissibleMiddleHeld =
  ECL.bridge→admissible currentShiftLyapunovReceiptMiddleHeld

currentShiftLyapunovDescent :
  EC.MDLAdmissible
    SRI.shiftExecutionContract
    SRI.shiftReceiptStart
    SRI.shiftReceiptNext
currentShiftLyapunovDescent =
  ECL.bridge→mdl currentShiftLyapunovReceipt

currentShiftLyapunovDescentNextMiddle :
  EC.MDLAdmissible
    SRI.shiftExecutionContract
    SRI.shiftReceiptNext
    SRI.shiftReceiptMiddle
currentShiftLyapunovDescentNextMiddle =
  ECL.bridge→mdl currentShiftLyapunovReceiptNextMiddle

currentShiftLyapunovDescentMiddleHeld :
  EC.MDLAdmissible
    SRI.shiftExecutionContract
    SRI.shiftReceiptMiddle
    SRI.shiftReceiptHeld
currentShiftLyapunovDescentMiddleHeld =
  ECL.bridge→mdl currentShiftLyapunovReceiptMiddleHeld
