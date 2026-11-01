module DASHI.Physics.Closure.PhysicsClosureEmpiricalBetaInstance where

open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.Closure.PhysicsClosureEmpirical as PCE
open import DASHI.Physics.MyRealInstance as MRI
open import DASHI.Physics.Closure.BetaSeamCertificatesInstance as BSCI
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC

-- Empirical closure instance that prefers beta-space seam certificates
-- while keeping the same RealClosureKit.
physicsClosureEmpiricalBeta : PCE.PhysicsClosureEmpirical
physicsClosureEmpiricalBeta =
  record
    { kit = MRI.myKit
    ; seams = λ {m} {k} → SSC.shiftSeams {m} {k}
    }

-- Optional: explicitly expose the beta seams separately.
betaSeams : ∀ {m k : Nat} → _
betaSeams {m} {k} = BSCI.betaSeamsShift {m} {k}
