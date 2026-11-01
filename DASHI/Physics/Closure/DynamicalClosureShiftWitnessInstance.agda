module DASHI.Physics.Closure.DynamicalClosureShiftWitnessInstance where

open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.Closure.PolarizationZLift as PZL

shiftDynamicsWitness : DCW.DynamicalClosureWitness
shiftDynamicsWitness =
  record
    { propagationSeams = λ {m} {k} → SSC.shiftSeams {m} {k}
    ; causalAdmissibilitySeams = λ {m} {k} → SSC.shiftSeams {m} {k}
    ; monotoneLyapunov = λ {m} {k} → MDLL.lyapunovShift {m} {k}
    ; monotoneFejer = MDLFA.mdlFejerShift
    ; effectiveGeometryOrthogonality = λ {m} → OZ.orthogonalityZLift {m}
    ; effectiveGeometryPolarization = λ {m} → PZL.polarizationZLift {m}
    }
