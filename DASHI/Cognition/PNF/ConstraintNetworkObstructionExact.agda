module DASHI.Cognition.PNF.ConstraintNetworkObstructionExact where

------------------------------------------------------------------------
-- GLOBAL C3 CONSTRAINT OBSTRUCTION
--
-- ConstraintPhaseFrustrationExact proves that raw phase mismatch need not be
-- costly.  Here we pass from one edge to a genuine finite network.  A triangle
-- requiring A=B, B=C, and A=next(C) is globally unsatisfiable: the first two
-- constraints force one common phase, while C3 has no fixed point under next.
--
-- With the indicator violation potential, every assignment therefore has
-- strictly positive total frustration, and cost one is attained.  This is an
-- exact obstruction/minimum theorem, not a biological claim.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_+_; _≤_; z≤n; s≤s)

import DASHI.Cognition.PNF.ConstraintPhaseFrustrationExact as Constraint
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

record TriangleAssignment : Set where
  constructor triangleAssignment
  field
    phaseA phaseB phaseC : Wheel.DepthWheelPhase

open TriangleAssignment public

record TriangleSatisfied (assignment : TriangleAssignment) : Set where
  constructor triangleSatisfied
  field
    abSame :
      Constraint.satisfies Constraint.samePhase
        (phaseA assignment) (phaseB assignment) ≡ true
    bcSame :
      Constraint.satisfies Constraint.samePhase
        (phaseB assignment) (phaseC assignment) ≡ true
    caNext :
      Constraint.satisfies Constraint.nextPhase
        (phaseC assignment) (phaseA assignment) ≡ true

open TriangleSatisfied public

noPhaseIsItsOwnNext :
  (phase : Wheel.DepthWheelPhase) →
  Wheel.nextDepthWheelPhase phase ≡ phase → ⊥
noPhaseIsItsOwnNext Wheel.phase-0 ()
noPhaseIsItsOwnNext Wheel.phase-1 ()
noPhaseIsItsOwnNext Wheel.phase-2 ()

phaseEqTrueImpliesEqual :
  (left right : Wheel.DepthWheelPhase) →
  Constraint.phaseEq left right ≡ true → left ≡ right
phaseEqTrueImpliesEqual Wheel.phase-0 Wheel.phase-0 refl = refl
phaseEqTrueImpliesEqual Wheel.phase-0 Wheel.phase-1 ()
phaseEqTrueImpliesEqual Wheel.phase-0 Wheel.phase-2 ()
phaseEqTrueImpliesEqual Wheel.phase-1 Wheel.phase-0 ()
phaseEqTrueImpliesEqual Wheel.phase-1 Wheel.phase-1 refl = refl
phaseEqTrueImpliesEqual Wheel.phase-1 Wheel.phase-2 ()
phaseEqTrueImpliesEqual Wheel.phase-2 Wheel.phase-0 ()
phaseEqTrueImpliesEqual Wheel.phase-2 Wheel.phase-1 ()
phaseEqTrueImpliesEqual Wheel.phase-2 Wheel.phase-2 refl = refl

triangleUnsatisfiable :
  (assignment : TriangleAssignment) → TriangleSatisfied assignment → ⊥
triangleUnsatisfiable assignment satisfied
  with phaseA assignment | phaseB assignment | phaseC assignment
... | Wheel.phase-0 | Wheel.phase-0 | Wheel.phase-0 =
  noPhaseIsItsOwnNext Wheel.phase-0
    (phaseEqTrueImpliesEqual Wheel.phase-1 Wheel.phase-0 (caNext satisfied))
... | Wheel.phase-0 | Wheel.phase-0 | Wheel.phase-1 =
  phaseEqTrueImpliesEqual Wheel.phase-0 Wheel.phase-1 (bcSame satisfied) |> impossible01
... | Wheel.phase-0 | Wheel.phase-0 | Wheel.phase-2 =
  phaseEqTrueImpliesEqual Wheel.phase-0 Wheel.phase-2 (bcSame satisfied) |> impossible02
... | Wheel.phase-0 | Wheel.phase-1 | c =
  phaseEqTrueImpliesEqual Wheel.phase-0 Wheel.phase-1 (abSame satisfied) |> impossible01
... | Wheel.phase-0 | Wheel.phase-2 | c =
  phaseEqTrueImpliesEqual Wheel.phase-0 Wheel.phase-2 (abSame satisfied) |> impossible02
... | Wheel.phase-1 | Wheel.phase-0 | c =
  phaseEqTrueImpliesEqual Wheel.phase-1 Wheel.phase-0 (abSame satisfied) |> impossible10
... | Wheel.phase-1 | Wheel.phase-1 | Wheel.phase-0 =
  phaseEqTrueImpliesEqual Wheel.phase-1 Wheel.phase-0 (bcSame satisfied) |> impossible10
... | Wheel.phase-1 | Wheel.phase-1 | Wheel.phase-1 =
  noPhaseIsItsOwnNext Wheel.phase-1
    (phaseEqTrueImpliesEqual Wheel.phase-2 Wheel.phase-1 (caNext satisfied))
... | Wheel.phase-1 | Wheel.phase-1 | Wheel.phase-2 =
  phaseEqTrueImpliesEqual Wheel.phase-1 Wheel.phase-2 (bcSame satisfied) |> impossible12
... | Wheel.phase-1 | Wheel.phase-2 | c =
  phaseEqTrueImpliesEqual Wheel.phase-1 Wheel.phase-2 (abSame satisfied) |> impossible12
... | Wheel.phase-2 | Wheel.phase-0 | c =
  phaseEqTrueImpliesEqual Wheel.phase-2 Wheel.phase-0 (abSame satisfied) |> impossible20
... | Wheel.phase-2 | Wheel.phase-1 | c =
  phaseEqTrueImpliesEqual Wheel.phase-2 Wheel.phase-1 (abSame satisfied) |> impossible21
... | Wheel.phase-2 | Wheel.phase-2 | Wheel.phase-0 =
  phaseEqTrueImpliesEqual Wheel.phase-2 Wheel.phase-0 (bcSame satisfied) |> impossible20
... | Wheel.phase-2 | Wheel.phase-2 | Wheel.phase-1 =
  phaseEqTrueImpliesEqual Wheel.phase-2 Wheel.phase-1 (bcSame satisfied) |> impossible21
... | Wheel.phase-2 | Wheel.phase-2 | Wheel.phase-2 =
  noPhaseIsItsOwnNext Wheel.phase-2
    (phaseEqTrueImpliesEqual Wheel.phase-0 Wheel.phase-2 (caNext satisfied))
  where
    infixl 0 _|>_
    _|>_ : ∀ {A B : Set} → A → (A → B) → B
    value |> f = f value

    impossible01 : Wheel.phase-0 ≡ Wheel.phase-1 → ⊥
    impossible01 ()
    impossible02 : Wheel.phase-0 ≡ Wheel.phase-2 → ⊥
    impossible02 ()
    impossible10 : Wheel.phase-1 ≡ Wheel.phase-0 → ⊥
    impossible10 ()
    impossible12 : Wheel.phase-1 ≡ Wheel.phase-2 → ⊥
    impossible12 ()
    impossible20 : Wheel.phase-2 ≡ Wheel.phase-0 → ⊥
    impossible20 ()
    impossible21 : Wheel.phase-2 ≡ Wheel.phase-1 → ⊥
    impossible21 ()

triangleFrustration : TriangleAssignment → Nat
triangleFrustration assignment =
  Constraint.violationCost Constraint.samePhase
    (phaseA assignment) (phaseB assignment)
  + Constraint.violationCost Constraint.samePhase
    (phaseB assignment) (phaseC assignment)
  + Constraint.violationCost Constraint.nextPhase
    (phaseC assignment) (phaseA assignment)

triangleFrustrationStrictlyPositive :
  (assignment : TriangleAssignment) → suc zero ≤ triangleFrustration assignment
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-0 Wheel.phase-0 Wheel.phase-0) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-0 Wheel.phase-0 Wheel.phase-1) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-0 Wheel.phase-0 Wheel.phase-2) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-0 Wheel.phase-1 Wheel.phase-0) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-0 Wheel.phase-1 Wheel.phase-1) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-0 Wheel.phase-1 Wheel.phase-2) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-0 Wheel.phase-2 Wheel.phase-0) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-0 Wheel.phase-2 Wheel.phase-1) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-0 Wheel.phase-2 Wheel.phase-2) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-1 Wheel.phase-0 Wheel.phase-0) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-1 Wheel.phase-0 Wheel.phase-1) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-1 Wheel.phase-0 Wheel.phase-2) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-1 Wheel.phase-1 Wheel.phase-0) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-1 Wheel.phase-1 Wheel.phase-1) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-1 Wheel.phase-1 Wheel.phase-2) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-1 Wheel.phase-2 Wheel.phase-0) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-1 Wheel.phase-2 Wheel.phase-1) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-1 Wheel.phase-2 Wheel.phase-2) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-2 Wheel.phase-0 Wheel.phase-0) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-2 Wheel.phase-0 Wheel.phase-1) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-2 Wheel.phase-0 Wheel.phase-2) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-2 Wheel.phase-1 Wheel.phase-0) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-2 Wheel.phase-1 Wheel.phase-1) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-2 Wheel.phase-1 Wheel.phase-2) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-2 Wheel.phase-2 Wheel.phase-0) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-2 Wheel.phase-2 Wheel.phase-1) = s≤s z≤n
triangleFrustrationStrictlyPositive
  (triangleAssignment Wheel.phase-2 Wheel.phase-2 Wheel.phase-2) = s≤s z≤n

costOneWitness : triangleFrustration
  (triangleAssignment Wheel.phase-0 Wheel.phase-0 Wheel.phase-0) ≡ 1
costOneWitness = refl
