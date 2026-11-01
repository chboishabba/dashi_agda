module DASHI.Physics.Closure.DynamicalClosureWitness where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat; _+_)

open import MDL.Core.Core as OldMDL
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.Closure.PolarizationZLift as PZL
open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record DynamicalClosureWitness : Setω where
  field
    propagationSeams : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    causalAdmissibilitySeams : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    monotoneLyapunov :
      ∀ {m k : Nat} →
      OldMDL.Lyapunov
        {S = RTC.Carrier (m + k)}
        (MDLParts.T (MSI.MDLPartsShift {m} {k}))
    monotoneFejer : MDLFA.MDLFejerAxiomsShift
    effectiveGeometryOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    effectiveGeometryPolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
