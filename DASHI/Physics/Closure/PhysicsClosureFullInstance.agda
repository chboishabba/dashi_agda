module DASHI.Physics.Closure.PhysicsClosureFullInstance where

open import Data.Unit as DU using (⊤; tt)
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_)

open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.MyRealInstance as MRI
open import DASHI.Geometry.QuadraticFormEmergence as QFE
open import DASHI.Geometry.SignatureUniqueness31 as SU
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Physics.Signature31InstanceShiftZ as Sig31
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarizationCoreInstance as QPCI
open import DASHI.Physics.Closure.PolarizationZLift as PZL
open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureShiftInstance as DCSI
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Signature31FromShiftOrbitProfile as S31OP
open import DASHI.Physics.Constraints.Generators as CG
open import DASHI.Physics.Constraints.Bracket as CB
open import DASHI.Physics.Constraints.Closure as CC
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.RealClosureKit as RK
open import Data.Nat using (z≤n)
open import MDL.Core.Core as OldMDL
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.UniversalityTheorem as UTH

-- Concrete instance: wires the Bool closure stack into PhysicsClosureFull.
-- The compatibility mdlLyap field remains generic, but the authoritative
-- Stage C Lyapunov witness lives in `dynamics`.

physicsClosureFull : PCF.PhysicsClosureFull
physicsClosureFull =
  record
    { kit = MRI.myKit
    ; metricEmergence = λ {ℓv} {ℓs} A F PD Ax → QFE.QuadraticFormEmergence A F PD Ax
    ; quadraticFormZ = λ {m} →
        proj₁
          (QFE.QuadraticFormEmergence
            (QES.AdditiveVecℤ {m})
            QES.ScalarFieldℤ
            (QES.PDzero {m})
            (QES.QuadraticEmergenceShiftAxioms {m}))
    ; polarizationZ = λ {m} → PZL.polarizationZLift {m}
    ; orthogonalityZ = λ {m} → OZ.orthogonalityZLift {m}
    ; signature31 = S31OP.signature31
    ; CS = CI.CS
    ; L = CI.L
    ; constraintClosure = CI.closure
    ; mdlLyap = λ {S} T → mdlLyapTrivial T
    ; mdlFejer = MDLFA.mdlFejerShift
    ; dynamics = DCSI.shiftDynamics
    ; universality = UTH.canonicalUniversality (RK.RealClosureKit.C MRI.myKit)
    }
  where
    mdlLyapTrivial : ∀ {S : Set} (T : S → S) → OldMDL.Lyapunov T
    mdlLyapTrivial T =
      record
        { L = λ _ → zero
        ; descent = λ _ → z≤n
        }

-- Concrete Lyapunov witness for the shift stack is available as:
-- MDLL.lyapunovShift {m} {k}

authoritativeLyapunovShift :
  ∀ {m k : Nat} →
  OldMDL.Lyapunov
    {S = RTC.Carrier (m + k)}
    (MDLParts.T (MSI.MDLPartsShift {m} {k}))
authoritativeLyapunovShift {m} {k} =
  DC.DynamicalClosure.lyapunovShift
    (PCF.PhysicsClosureFull.dynamics physicsClosureFull)
    {m} {k}
