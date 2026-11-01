module DASHI.Physics.Closure.PhysicsClosureInstanceAssumed where

open import Data.Unit as DU using (⊤; tt)
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import DASHI.Physics.Closure.PhysicsClosure as PC
open import DASHI.Physics.MyRealInstance as MRI
open import DASHI.Geometry.QuadraticFormFromProjection as QFP
open import DASHI.Physics.Signature31Canonical as S31C
open import DASHI.Physics.Constraints.Generators as CG
open import DASHI.Physics.Constraints.Bracket as CB
open import DASHI.Physics.Constraints.Closure as CC
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Closure.ConstraintClosureFromCanonicalPathTheorem as CCFCPT
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.RealTernaryCarrier as RTC
open import MDL.Core.Core as OldMDL
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Physics.UniversalityTheorem as UTH
open import DASHI.Physics.RealClosureKit as RK

-- Legacy assumed closure instance. Signature comes from the canonical
-- intrinsic-core theorem path; constraint closure and Lyapunov witness reuse
-- the same concrete shift witnesses as the canonical full-closure path.
physicsClosureAssumed : PC.PhysicsClosure
physicsClosureAssumed =
  record
    { kit = MRI.myKit
    ; metricEmergence = record
        { build = λ {A} PD → record
            { A = A
            ; Q = λ _ → 0
            ; parallelogram = record { paral = ⊤ }
            }
        }
    ; orthogonalityZ = λ {m} → OZ.orthogonalityZLift {m}
    ; signature31 = S31C.signature31-theorem
    ; CS = CI.CS
    ; L = CI.L
    ; constraintClosure = CCFCPT.canonicalPathInducedConstraintClosure
    ; mdlLyap = λ {m} {k} → MDLL.lyapunovShift {m} {k}
    ; universality = UTH.canonicalUniversality (RK.RealClosureKit.C MRI.myKit)
    }

physicsClosureAssumedDefault : PC.PhysicsClosure
physicsClosureAssumedDefault = physicsClosureAssumed

-- Explicit compatibility alias for legacy imports.
legacyPhysicsClosureCompatibility : PC.PhysicsClosure
legacyPhysicsClosureCompatibility = physicsClosureAssumed
