module DASHI.Physics.Closure.PhysicsClosureInstanceAssumed where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import DASHI.Physics.Closure.PhysicsClosure as PC
open import DASHI.Physics.MyRealInstance as MRI
open import DASHI.Geometry.QuadraticFormFromProjection as QFP
open import DASHI.Geometry.SignatureUniqueness31 as SU
open import DASHI.Physics.SignatureUniquenessAssumed as SUA
open import DASHI.Physics.Constraints.Generators as CG
open import DASHI.Physics.Constraints.Bracket as CB
open import DASHI.Physics.Constraints.Closure as CC
open import DASHI.Physics.UniversalityTheorem as UTH

-- Concrete instance: wires the Bool closure stack into PhysicsClosure,
-- using the assumption-based signature law.
physicsClosureAssumed : SUA.SignatureAssumedAxioms → PC.PhysicsClosure
physicsClosureAssumed ax =
  record
    { kit = MRI.myKit
    ; metricEmergence = record
        { build = λ {A} PD → record
            { A = A
            ; Q = λ _ → 0
            ; parallelogram = record { paral = ⊤ }
            }
        }
    ; orthogonality = ⊤
    ; signature31 = SUA.signature31-assumed ax
    ; CS = record
        { Constraint = ⊤
        ; actsOn = λ X → X
        ; apply = λ {S} _ x → x
        }
    ; L = record
        { _[_,]_ = λ _ _ → tt
        ; antisym = ⊤
        ; jacobi = ⊤
        }
    ; constraintClosure = record { closes = λ _ _ → (tt , refl) }
    ; mdlLyap = λ {S} T → ⊤
    ; universality = record { statement = ⊤ }
    }

physicsClosureAssumedDefault : PC.PhysicsClosure
physicsClosureAssumedDefault =
  physicsClosureAssumed SUA.signatureAssumedAxioms
