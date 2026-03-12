module DASHI.Physics.Closure.DynamicalClosureShiftInstance where

open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.ContractionDiffusionPair as CDP
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import Agda.Builtin.Nat using (_+_; Nat)

shiftDynamics : DC.DynamicalClosure
shiftDynamics =
  record
    { seams = λ {m} {k} → SSC.shiftSeams {m} {k}
    ; lyapunovShift = λ {m} {k} → MDLL.lyapunovShift {m} {k}
    ; contractionDiffusion = λ {m} {k} →
        CDP.mkContractionDiffusionPair
          (MDLParts.T (MSI.MDLPartsShift {m} {k}))
          (λ x → x)
    ; mdlFejerWitness = MDLFA.mdlFejerShift
    ; status =
        record
          { propagation = DCS.fiberBackedPropagation
          ; causalAdmissibility = DCS.seamBackedCausalAdmissibility
          ; monotoneQuantity = DCS.mdlLyapunovAndFejer
          ; effectiveGeometry = DCS.quadraticPolarizationAndOrthogonality
          }
    }
