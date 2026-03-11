module DASHI.Physics.Closure.PhysicsClosureInstanceAssumed where

open import Data.Unit as DU using (⊤; tt)
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import DASHI.Physics.Closure.PhysicsClosure as PC
open import DASHI.Physics.MyRealInstance as MRI
open import DASHI.Geometry.QuadraticFormFromProjection as QFP
open import DASHI.Geometry.SignatureUniqueness31 as SU
import DASHI.Physics.Signature31FromShiftOrbitProfile as S31OP
open import DASHI.Physics.Constraints.Generators as CG
open import DASHI.Physics.Constraints.Bracket as CB
open import DASHI.Physics.Constraints.Closure as CC
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Closure.MDLLyapunovCompatibility as MDLC
open import DASHI.Physics.UniversalityTheorem as UTH
open import DASHI.Physics.RealClosureKit as RK

-- Legacy assumed closure instance. Signature still comes from the concrete
-- shift-orbit theorem path; constraint closure now reuses the same concrete
-- witness as the canonical full-closure path.
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
    ; signature31 = S31OP.signature31-theorem
    ; CS = CI.CS
    ; L = CI.L
    ; constraintClosure = CI.closure
    ; mdlLyap = λ {S} T → MDLC.mdlLyapTrivial T
    ; universality = UTH.canonicalUniversality (RK.RealClosureKit.C MRI.myKit)
    }

physicsClosureAssumedDefault : PC.PhysicsClosure
physicsClosureAssumedDefault = physicsClosureAssumed
