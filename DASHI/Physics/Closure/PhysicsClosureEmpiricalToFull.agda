module DASHI.Physics.Closure.PhysicsClosureEmpiricalToFull where

open import Data.Unit as DU using (⊤; tt)
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import Data.Product using (_,_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.Closure.PhysicsClosureEmpirical as PCE
open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Physics.Constraints.Generators as CG
open import DASHI.Physics.Constraints.Bracket as CB
open import DASHI.Physics.Constraints.Closure as CC
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL
open import DASHI.Physics.Closure.MDLLyapunovCompatibility as MDLC
open import DASHI.Physics.Closure.DynamicalClosureShiftInstance as DCSI
open import DASHI.Physics.UniversalityTheorem as UTH
open import MDL.Core.Core as OldMDL
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarizationCoreInstance as QPCI
open import DASHI.Physics.Closure.PolarizationZLift as PZL
open import DASHI.Physics.RealClosureKit as RK
open import DASHI.Physics.Signature31FromShiftOrbitProfile as S31OP
open import DASHI.Physics.Constraints.ConcreteInstance as CI

-- Adapter: embeds empirical closure seams into the full closure package.
--
-- Note: PhysicsClosureFull.mdlLyap is a generic Set-valued field. We keep it
-- as a compatibility fallback here. The authoritative Stage C witness is
-- `MDLL.lyapunovShift`. Constraint closure on the canonical path now reuses
-- the same concrete witness as PhysicsClosureFullInstance.

mdlLyapShiftWitness :
  ∀ {m k : Nat} →
  OldMDL.Lyapunov
    {S = RTC.Carrier (m + k)}
    (MDLParts.T (MSI.MDLPartsShift {m} {k}))
mdlLyapShiftWitness {m} {k} = MDLL.lyapunovShift {m} {k}

empiricalToFull : PCE.PhysicsClosureEmpirical → PCF.PhysicsClosureFull
empiricalToFull emp =
  record
    { kit = PCE.kit emp
    ; metricEmergence = λ {ℓv} {ℓs} A F Pkg →
        PDP.quadraticFromProjectionDefect A F Pkg
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
    ; signature31 = S31OP.signature31
    ; CS = CI.CS
    ; L = CI.L
    ; constraintClosure = CI.closure
    ; mdlLyap = λ {S} T → MDLC.mdlLyapTrivial T
    ; mdlFejer = MDLFA.mdlFejerShift
    ; dynamics = DCSI.shiftDynamics
    ; universality = UTH.canonicalUniversality (RK.RealClosureKit.C (PCE.kit emp))
    }

authoritativeLyapunovShift :
  ∀ {m k : Nat} (emp : PCE.PhysicsClosureEmpirical) →
  OldMDL.Lyapunov
    {S = RTC.Carrier (m + k)}
    (MDLParts.T (MSI.MDLPartsShift {m} {k}))
authoritativeLyapunovShift {m} {k} _ =
  mdlLyapShiftWitness {m} {k}
