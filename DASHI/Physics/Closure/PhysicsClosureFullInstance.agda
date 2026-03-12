module DASHI.Physics.Closure.PhysicsClosureFullInstance where

-- Assumptions:
-- - concrete real-kit instance and shift-side dynamics/constraint witnesses
-- - projection-defect/parallelogram route for quadratic emergence
--
-- Output:
-- - concrete PhysicsClosureFull instance used by canonical minimal-credible
--   closure.
--
-- Classification:
-- - concrete

open import Data.Unit as DU using (⊤; tt)
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import Agda.Builtin.Nat using (Nat; zero; _+_)

open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.MyRealInstance as MRI
open import DASHI.Physics.Closure.PolarizationZLift as PZL
open import DASHI.Physics.Closure.DynamicalClosureShiftInstance as DCSI
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL
open import DASHI.Physics.Closure.MDLLyapunovCompatibility as MDLC
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.RealClosureKit as RK
open import MDL.Core.Core as OldMDL
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.UniversalityTheorem as UTH

-- Concrete instance: wires the Bool closure stack into PhysicsClosureFull.
-- The compatibility mdlLyap field remains generic, but the authoritative
-- Stage C Lyapunov witness is exposed through `MDLL.lyapunovShift`.

physicsClosureFull : PCF.PhysicsClosureFull
physicsClosureFull =
  PCF.canonicalPhysicsClosureFullFromExternal
    record
      { kit = MRI.myKit
      ; polarizationZ = λ {m} → PZL.polarizationZLift {m}
      ; orthogonalityZ = λ {m} → OZ.orthogonalityZLift {m}
      ; mdlLyap = λ {S} T → MDLC.mdlLyapTrivial T
      ; mdlFejer = MDLFA.mdlFejerShift
      ; dynamics = DCSI.shiftDynamics
      ; universality = UTH.canonicalUniversality (RK.RealClosureKit.C MRI.myKit)
      }

-- Concrete Lyapunov witness for the shift stack is available as:
-- MDLL.lyapunovShift {m} {k}

authoritativeLyapunovShift :
  ∀ {m k : Nat} →
  OldMDL.Lyapunov
    {S = RTC.Carrier (m + k)}
    (MDLParts.T (MSI.MDLPartsShift {m} {k}))
authoritativeLyapunovShift {m} {k} =
  MDLL.lyapunovShift {m} {k}
