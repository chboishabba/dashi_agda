module DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier where

------------------------------------------------------------------------
-- Concrete su(2) carrier and adjoint action.
--
-- The group SU(2) is the unit-quaternion carrier from
-- `BalabanSU2QuaternionCarrier`.  Its Lie algebra is represented by the
-- three imaginary quaternion coordinates.  The action
--
--   Ad_u X = u X conjugate(u)
--
-- is defined literally and all additive/group-action laws below are reduced
-- to polynomial identities over the same commutative-ring socket already used
-- by the quaternion carrier.  No additional postulate or analytic theorem is
-- introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (+-assoc; +-identityˡ; +-identityʳ)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using (-‿inverseʳ; zeroʳ)

open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( zeroCoefficient
  ; module RealPolynomialSolver
  )
open RealPolynomialSolver using
  ( Polynomial
  ; solve
  ; _:=_
  ; _:+_
  ; _:*_
  ; con
  ; :-_
  )

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanLatticeAdjointCovariantDerivative using
  ( AdjointAdditiveModule )
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( AdjointLinearModule )
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( Quaternion
  ; quat
  ; q0
  ; q1
  ; q2
  ; q3
  ; _+R_
  ; _*R_
  ; -R_
  ; zeroR
  ; realSolverRing
  ; q0Multiply
  ; q1Multiply
  ; q2Multiply
  ; q3Multiply
  ; q0Conjugate
  ; q1Conjugate
  ; q2Conjugate
  ; q3Conjugate
  ; _+q_
  ; conjugateQ
  ; _*q_
  ; quaternionOneLeft
  ; quaternionOneRight
  ; oneQ
  ; -0#≈0#
  ; oneRight1
  ; oneRight2
  ; oneRight3
  ; SU2Quaternion
  ; su2q
  ; quaternion
  ; su2Identity
  ; su2Multiply
  ; su2QuaternionGroup
  )

record SU2LieAlgebra : Set where
  constructor su2Lie
  field
    xComponent : ℝ
    yComponent : ℝ
    zComponent : ℝ

open SU2LieAlgebra public

su2LieExt :
  ∀ {X Y : SU2LieAlgebra} →
  xComponent X ≡ xComponent Y →
  yComponent X ≡ yComponent Y →
  zComponent X ≡ zComponent Y →
  X ≡ Y
su2LieExt {su2Lie x y z} {su2Lie .x .y .z} refl refl refl = refl

lieQuaternion : SU2LieAlgebra → Quaternion
lieQuaternion (su2Lie x y z) = quat zeroR x y z

lieFromQuaternion : Quaternion → SU2LieAlgebra
lieFromQuaternion q = su2Lie (q1 q) (q2 q) (q3 q)

lieFromQuaternionLieQuaternion :
  ∀ X → lieFromQuaternion (lieQuaternion X) ≡ X
lieFromQuaternionLieQuaternion (su2Lie x y z) = refl

lieZero : SU2LieAlgebra
lieZero = su2Lie zeroR zeroR zeroR

lieAdd : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
lieAdd (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  su2Lie (x₁ +R x₂) (y₁ +R y₂) (z₁ +R z₂)

lieNegate : SU2LieAlgebra → SU2LieAlgebra
lieNegate (su2Lie x y z) = su2Lie (-R x) (-R y) (-R z)

lieSubtract : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
lieSubtract X Y = lieAdd X (lieNegate Y)

lieScale : ℝ → SU2LieAlgebra → SU2LieAlgebra
lieScale scalar (su2Lie x y z) =
  su2Lie (scalar *R x) (scalar *R y) (scalar *R z)

lieAddAssociative :
  ∀ X Y Z → lieAdd (lieAdd X Y) Z ≡ lieAdd X (lieAdd Y Z)
lieAddAssociative
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  (su2Lie x₃ y₃ z₃) =
  su2LieExt
    (+-assoc x₁ x₂ x₃)
    (+-assoc y₁ y₂ y₃)
    (+-assoc z₁ z₂ z₃)

lieZeroLeft : ∀ X → lieAdd lieZero X ≡ X
lieZeroLeft (su2Lie x y z) =
  su2LieExt
    (+-identityˡ x)
    (+-identityˡ y)
    (+-identityˡ z)

lieZeroRight : ∀ X → lieAdd X lieZero ≡ X
lieZeroRight (su2Lie x y z) =
  su2LieExt
    (+-identityʳ x)
    (+-identityʳ y)
    (+-identityʳ z)

adjointQuaternion :
  SU2Quaternion → SU2LieAlgebra → Quaternion
adjointQuaternion u X =
  (quaternion u *q lieQuaternion X) *q conjugateQ (quaternion u)

su2Adjoint :
  SU2Quaternion → SU2LieAlgebra → SU2LieAlgebra
su2Adjoint u X = lieFromQuaternion (adjointQuaternion u X)

-- After expanding both quaternion products, the real component contains only
-- the twelve cancelling monomials below.  In particular, the intermediate
-- pure-imaginary component is not represented by terms such as 0 * x or x +
-- 0; those terms have already been removed with the real-ring laws.
adjointInner0 :
  ∀ a₀ a₁ a₂ a₃ x y z →
  q0 (quat a₀ a₁ a₂ a₃ *q quat zeroR x y z)
    ≡
  ((-R (a₁ *R x)) +R (-R (a₂ *R y))) +R (-R (a₃ *R z))
adjointInner0 a₀ a₁ a₂ a₃ x y z
  rewrite q0Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
        | zeroʳ a₀
        | +-identityˡ (-R (a₁ *R x)) =
  refl

adjointInner1 :
  ∀ a₀ a₁ a₂ a₃ x y z →
  q1 (quat a₀ a₁ a₂ a₃ *q quat zeroR x y z)
    ≡
  ((a₀ *R x) +R (a₂ *R z)) +R (-R (a₃ *R y))
adjointInner1 a₀ a₁ a₂ a₃ x y z
  rewrite q1Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
        | zeroʳ a₁
        | +-identityʳ (a₀ *R x) =
  refl

adjointInner2 :
  ∀ a₀ a₁ a₂ a₃ x y z →
  q2 (quat a₀ a₁ a₂ a₃ *q quat zeroR x y z)
    ≡
  ((a₀ *R y) +R (-R (a₁ *R z))) +R (a₃ *R x)
adjointInner2 a₀ a₁ a₂ a₃ x y z
  rewrite q2Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
        | zeroʳ a₂
        | +-identityʳ ((a₀ *R y) +R (-R (a₁ *R z))) =
  refl

adjointInner3 :
  ∀ a₀ a₁ a₂ a₃ x y z →
  q3 (quat a₀ a₁ a₂ a₃ *q quat zeroR x y z)
    ≡
  ((a₀ *R z) +R (a₁ *R y)) +R (-R (a₂ *R x))
adjointInner3 a₀ a₁ a₂ a₃ x y z
  rewrite q3Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
        | zeroʳ a₃
        | +-identityʳ
            (((a₀ *R z) +R (a₁ *R y)) +R (-R (a₂ *R x))) =
  refl

adjointQuaternionRealPartPolynomial :
  ∀ a₀ a₁ a₂ a₃ x y z →
  ((((
       (((-R ((a₁ *R x))) +R (-R ((a₂ *R y)))) +R (-R ((a₃ *R z)))) *R a₀)
       +R (-R (((((a₀ *R x) +R (a₂ *R z)) +R (-R (a₃ *R y))) *R (-R a₁)))))
       +R (-R (((((a₀ *R y) +R (-R (a₁ *R z))) +R (a₃ *R x)) *R (-R a₂)))))
       +R (-R (((((a₀ *R z) +R (a₁ *R y)) +R (-R (a₂ *R x))) *R (-R a₃)))))
    ≡ a₀ +R (-R a₀)
adjointQuaternionRealPartPolynomial =
  solve 7
    (λ a₀ a₁ a₂ a₃ x y z →
      (((
        (((((:- ((a₁ :* x)) :+ :- ((a₂ :* y))) :+ :- ((a₃ :* z))) :* a₀)))
        :+ :- (((((a₀ :* x) :+ (a₂ :* z)) :+ :- (a₃ :* y)) :* :- a₁)))
        :+ :- (((((a₀ :* y) :+ :- ((a₁ :* z))) :+ (a₃ :* x)) :* :- a₂)))
        :+ :- (((((a₀ :* z) :+ (a₁ :* y)) :+ :- ((a₂ :* x))) :* :- a₃)))
      := (a₀ :+ (:- a₀)))
    refl

adjointPureImaginaryCancellation :
  ∀ a₀ a₁ a₂ a₃ x y z →
  (((((((((((
      (-R ((a₀ *R a₁) *R x))
      +R (-R ((a₀ *R a₂) *R y)))
      +R (-R ((a₀ *R a₃) *R z)))
      +R ((a₁ *R a₀) *R x))
      +R ((a₁ *R a₂) *R z))
      +R (-R ((a₁ *R a₃) *R y)))
      +R ((a₂ *R a₀) *R y))
      +R (-R ((a₂ *R a₁) *R z)))
      +R ((a₂ *R a₃) *R x))
      +R ((a₃ *R a₀) *R z))
      +R ((a₃ *R a₁) *R y))
      +R (-R ((a₃ *R a₂) *R x)))
    ≡ a₀ +R (-R a₀)
adjointPureImaginaryCancellation =
  solve 7
    (λ a₀ a₁ a₂ a₃ x y z →
      (((((((((((
        :- ((a₀ :* a₁) :* x)
        :+ :- ((a₀ :* a₂) :* y))
        :+ :- ((a₀ :* a₃) :* z))
        :+ ((a₁ :* a₀) :* x))
        :+ ((a₁ :* a₂) :* z))
        :+ :- ((a₁ :* a₃) :* y))
        :+ ((a₂ :* a₀) :* y))
        :+ :- ((a₂ :* a₁) :* z))
        :+ ((a₂ :* a₃) :* x))
        :+ ((a₃ :* a₀) :* z))
        :+ ((a₃ :* a₁) :* y))
        :+ :- ((a₃ :* a₂) :* x))
      := (a₀ :+ (:- a₀)))
    refl

-- The four component formulae expose the nested quaternion product.  Ring
-- normalization removes the zero coordinates of lieQuaternion and connects
-- that expansion to the zero-free cancellation above.
adjointQuaternionRealPartExpanded :
  ∀ a₀ a₁ a₂ a₃ x y z →
  q0 ((quat a₀ a₁ a₂ a₃ *q quat zeroR x y z)
      *q conjugateQ (quat a₀ a₁ a₂ a₃))
    ≡
  (((((((((((
      (-R ((a₀ *R a₁) *R x))
      +R (-R ((a₀ *R a₂) *R y)))
      +R (-R ((a₀ *R a₃) *R z)))
      +R ((a₁ *R a₀) *R x))
      +R ((a₁ *R a₂) *R z))
      +R (-R ((a₁ *R a₃) *R y)))
      +R ((a₂ *R a₀) *R y))
      +R (-R ((a₂ *R a₁) *R z)))
      +R ((a₂ *R a₃) *R x))
      +R ((a₃ *R a₀) *R z))
      +R ((a₃ *R a₁) *R y))
      +R (-R ((a₃ *R a₂) *R x)))
adjointQuaternionRealPartExpanded a₀ a₁ a₂ a₃ x y z
  rewrite q0Multiply (quat a₀ a₁ a₂ a₃ *q quat zeroR x y z) (conjugateQ (quat a₀ a₁ a₂ a₃))
    | adjointInner0 a₀ a₁ a₂ a₃ x y z
    | adjointInner1 a₀ a₁ a₂ a₃ x y z
    | adjointInner2 a₀ a₁ a₂ a₃ x y z
    | adjointInner3 a₀ a₁ a₂ a₃ x y z
    | q0Conjugate (quat a₀ a₁ a₂ a₃)
    | q1Conjugate (quat a₀ a₁ a₂ a₃)
    | q2Conjugate (quat a₀ a₁ a₂ a₃)
    | q3Conjugate (quat a₀ a₁ a₂ a₃) =
  trans
    (adjointQuaternionRealPartPolynomial a₀ a₁ a₂ a₃ x y z)
    (sym (adjointPureImaginaryCancellation a₀ a₁ a₂ a₃ x y z))

adjointQuaternionPureImaginary :
  ∀ u X → q0 (adjointQuaternion u X) ≡ zeroR
adjointQuaternionPureImaginary
  (su2q (quat a₀ a₁ a₂ a₃) a-unit)
  (su2Lie x y z) =
  trans
    (adjointQuaternionRealPartExpanded a₀ a₁ a₂ a₃ x y z)
    (trans
      (adjointPureImaginaryCancellation a₀ a₁ a₂ a₃ x y z)
      (-‿inverseʳ a₀))

lieQuaternionAdjoint :
  ∀ u X → lieQuaternion (su2Adjoint u X) ≡ adjointQuaternion u X
lieQuaternionAdjoint u X =
  DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier.quaternionExt
    (sym (adjointQuaternionPureImaginary u X))
    refl refl refl

su2AdjointUnit :
  ∀ X → su2Adjoint su2Identity X ≡ X
su2IdentityConjugate : conjugateQ (quaternion su2Identity) ≡ oneQ
su2IdentityConjugate =
  DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier.quaternionExt
    refl
    -0#≈0#
    -0#≈0#
    -0#≈0#

su2AdjointUnit (su2Lie x y z) =
  su2LieExt
    (cong q1
      (trans
        (cong (λ q → q *q conjugateQ (quaternion su2Identity))
          (quaternionOneLeft (lieQuaternion (su2Lie x y z))))
        (trans
          (cong (λ q → lieQuaternion (su2Lie x y z) *q q)
            su2IdentityConjugate)
          (quaternionOneRight (lieQuaternion (su2Lie x y z))))))
    (cong q2
      (trans
        (cong (λ q → q *q conjugateQ (quaternion su2Identity))
          (quaternionOneLeft (lieQuaternion (su2Lie x y z))))
        (trans
          (cong (λ q → lieQuaternion (su2Lie x y z) *q q)
            su2IdentityConjugate)
          (quaternionOneRight (lieQuaternion (su2Lie x y z))))))
    (cong q3
      (trans
        (cong (λ q → q *q conjugateQ (quaternion su2Identity))
          (quaternionOneLeft (lieQuaternion (su2Lie x y z))))
        (trans
          (cong (λ q → lieQuaternion (su2Lie x y z) *q q)
            su2IdentityConjugate)
          (quaternionOneRight (lieQuaternion (su2Lie x y z))))))

su2AdjointMultiply :
  ∀ u v X →
  su2Adjoint (su2Multiply u v) X
    ≡ su2Adjoint u (su2Adjoint v X)
su2AdjointMultiply
  (su2q (quat a₀ a₁ a₂ a₃) a-unit)
  (su2q (quat b₀ b₁ b₂ b₃) b-unit)
  (su2Lie x y z) =
  su2LieExt
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       x ∷ y ∷ z ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       x ∷ y ∷ z ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       x ∷ y ∷ z ∷ [])
      realSolverRing)

su2AdjointAdd :
  ∀ u X Y →
  su2Adjoint u (lieAdd X Y)
    ≡ lieAdd (su2Adjoint u X) (su2Adjoint u Y)
su2AdjointAdd
  (su2q (quat a₀ a₁ a₂ a₃) a-unit)
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x₁ ∷ y₁ ∷ z₁ ∷
       x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x₁ ∷ y₁ ∷ z₁ ∷
       x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x₁ ∷ y₁ ∷ z₁ ∷
       x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)

su2AdjointSubtract :
  ∀ u X Y →
  su2Adjoint u (lieSubtract X Y)
    ≡ lieSubtract (su2Adjoint u X) (su2Adjoint u Y)
su2AdjointSubtract
  (su2q (quat a₀ a₁ a₂ a₃) a-unit)
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x₁ ∷ y₁ ∷ z₁ ∷
       x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x₁ ∷ y₁ ∷ z₁ ∷
       x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ x₁ ∷ y₁ ∷ z₁ ∷
       x₂ ∷ y₂ ∷ z₂ ∷ [])
      realSolverRing)

su2AdjointZero : ∀ u → su2Adjoint u lieZero ≡ lieZero
su2AdjointZero (su2q (quat a₀ a₁ a₂ a₃) a-unit) =
  su2LieExt
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) realSolverRing)

su2AdjointScale :
  ∀ u scalar X →
  su2Adjoint u (lieScale scalar X)
    ≡ lieScale scalar (su2Adjoint u X)
su2AdjointScale
  (su2q (quat a₀ a₁ a₂ a₃) a-unit)
  scalar
  (su2Lie x y z) =
  su2LieExt
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ scalar ∷ x ∷ y ∷ z ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ scalar ∷ x ∷ y ∷ z ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ scalar ∷ x ∷ y ∷ z ∷ [])
      realSolverRing)

su2AdjointAdditiveModule :
  AdjointAdditiveModule su2QuaternionGroup
su2AdjointAdditiveModule = record
  { Vector = SU2LieAlgebra
  ; subtract = lieSubtract
  ; action = su2Adjoint
  ; actionUnit = su2AdjointUnit
  ; actionMultiply = su2AdjointMultiply
  ; actionSubtract = su2AdjointSubtract
  }

su2AdjointLinearModule :
  AdjointLinearModule su2QuaternionGroup
su2AdjointLinearModule = record
  { additive = su2AdjointAdditiveModule
  ; zeroVector = lieZero
  ; addVector = lieAdd
  ; addAssociative = lieAddAssociative
  ; zeroLeft = lieZeroLeft
  ; zeroRight = lieZeroRight
  ; actionZero = su2AdjointZero
  ; actionAdd = su2AdjointAdd
  }
