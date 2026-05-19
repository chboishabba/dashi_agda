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
-- The theorem-facing surface below is the current canonical shift bridge.
abstract
  mdlLyapTrivial : ∀ {S : Set} (T : S → S) → OldMDL.Lyapunov T
  mdlLyapTrivial T =
    record
      { L = λ _ → zero
      ; descent = λ _ → z≤n
      }

-- Current live bridge: the shift-side Lyapunov witness is exposed directly on
-- the execution-contract surface and paired with the concrete execution receipt
-- that already certifies the live shift step.
currentShiftLyapunovReceipt :
  ECL.ExecutionContractLyapunovReceipt
    SRI.shiftExecutionContract
    SRI.shiftReceiptStart
    SRI.shiftReceiptNext
currentShiftLyapunovReceipt = record
  { sourceLyapunov =
      MDLL.lyapunovShift
        {m = suc zero}
        {k = suc (suc (suc zero))}
  ; receipt = SRI.shiftExecutionReceipt
  }

currentShiftLyapunovAdmissible :
  EC.AdmissibleStep
    SRI.shiftExecutionContract
    SRI.shiftReceiptStart
    SRI.shiftReceiptNext
currentShiftLyapunovAdmissible =
  ECL.bridge→admissible currentShiftLyapunovReceipt

currentShiftLyapunovDescent :
  EC.MDLAdmissible
    SRI.shiftExecutionContract
    SRI.shiftReceiptStart
    SRI.shiftReceiptNext
currentShiftLyapunovDescent =
  ECL.bridge→mdl currentShiftLyapunovReceipt
