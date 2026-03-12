module DASHI.Physics.Closure.PhysicsClosureFullShiftInstance where

open import Data.Unit as DU using (⊤; tt)
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ

open import DASHI.Physics.Closure.PhysicsClosureFullShift as PCFS
open import DASHI.Physics.TernaryRealInstanceShift as TRIS
open import DASHI.Geometry.SignatureUniqueness31 using (sig31)
open import DASHI.Physics.Closure.DynamicalClosureShiftInstance as DCSI
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.UniversalityTheorem as UTH
open import DASHI.Physics.RealClosureKitFiber as RKF
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage as CCFP
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarizationCoreInstance as QPCI
open import DASHI.Physics.Closure.PolarizationZLift as PZL
open import Data.Product using (proj₁)
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP

-- Concrete shift-closure instance with real Lyapunov witness.
physicsClosureFullShift : PCFS.PhysicsClosureFullShift
physicsClosureFullShift =
  record
    { kit = TRIS.realKitFiber
    ; signature31 = sig31
    ; mdlLyap = λ {m} {k} → MDLL.lyapunovShift {m} {k}
    ; mdlFejer = MDLFA.mdlFejerShift
    ; dynamics = DCSI.shiftDynamics
    ; quadraticFormZ = λ {m} →
        let
          pkg =
            PDP.fromEmergenceAxioms
              (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
              (QES.PDzero {m})
              (QES.QuadraticEmergenceShiftAxioms {m})
        in
        proj₁
          (PDP.quadraticFromProjectionDefect
            (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ pkg)
    ; polarizationZ = λ {m} → PZL.polarizationZLift {m}
    ; orthogonalityZ = λ {m} → OZ.orthogonalityZLift {m}
    ; CS = CI.CS
    ; L = CI.L
    ; constraintClosure = CCFP.canonicalPackageInducedClosure
    ; universality = UTH.canonicalUniversality (RKF.RealClosureKitFiber.C TRIS.realKitFiber)
    }
