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
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  (-‿inverseʳ; zeroˡ; zeroʳ; [-x][-y]≈xy)

open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( zeroCoefficient
  ; module RealPolynomialSolver
  )
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  ( conjugateProduct1Polynomial
  ; conjugateProduct2Polynomial
  ; conjugateProduct3Polynomial
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
  ; quaternionMultiplyAssociative
  ; quaternionExt
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

quaternionMultiplyAddLeft :
  ∀ a b c → a *q (b +q c) ≡ (a *q b) +q (a *q c)
quaternionMultiplyAddLeft
  (quat a₀ a₁ a₂ a₃)
  (quat b₀ b₁ b₂ b₃)
  (quat c₀ c₁ c₂ c₃)
  rewrite q0Multiply (quat a₀ a₁ a₂ a₃)
    (quat b₀ b₁ b₂ b₃ +q quat c₀ c₁ c₂ c₃)
    | q0Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q0Multiply (quat a₀ a₁ a₂ a₃) (quat c₀ c₁ c₂ c₃)
    | q1Multiply (quat a₀ a₁ a₂ a₃)
      (quat b₀ b₁ b₂ b₃ +q quat c₀ c₁ c₂ c₃)
    | q1Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q1Multiply (quat a₀ a₁ a₂ a₃) (quat c₀ c₁ c₂ c₃)
    | q2Multiply (quat a₀ a₁ a₂ a₃)
      (quat b₀ b₁ b₂ b₃ +q quat c₀ c₁ c₂ c₃)
    | q2Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q2Multiply (quat a₀ a₁ a₂ a₃) (quat c₀ c₁ c₂ c₃)
    | q3Multiply (quat a₀ a₁ a₂ a₃)
      (quat b₀ b₁ b₂ b₃ +q quat c₀ c₁ c₂ c₃)
    | q3Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q3Multiply (quat a₀ a₁ a₂ a₃) (quat c₀ c₁ c₂ c₃) =
  quaternionExt
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])
      realSolverRing)

quaternionMultiplyAddRight :
  ∀ a b c → (a +q b) *q c ≡ (a *q c) +q (b *q c)
quaternionMultiplyAddRight
  (quat a₀ a₁ a₂ a₃)
  (quat b₀ b₁ b₂ b₃)
  (quat c₀ c₁ c₂ c₃)
  rewrite q0Multiply (quat a₀ a₁ a₂ a₃ +q quat b₀ b₁ b₂ b₃)
    (quat c₀ c₁ c₂ c₃)
    | q0Multiply (quat a₀ a₁ a₂ a₃) (quat c₀ c₁ c₂ c₃)
    | q0Multiply (quat b₀ b₁ b₂ b₃) (quat c₀ c₁ c₂ c₃)
    | q1Multiply (quat a₀ a₁ a₂ a₃ +q quat b₀ b₁ b₂ b₃)
      (quat c₀ c₁ c₂ c₃)
    | q1Multiply (quat a₀ a₁ a₂ a₃) (quat c₀ c₁ c₂ c₃)
    | q1Multiply (quat b₀ b₁ b₂ b₃) (quat c₀ c₁ c₂ c₃)
    | q2Multiply (quat a₀ a₁ a₂ a₃ +q quat b₀ b₁ b₂ b₃)
      (quat c₀ c₁ c₂ c₃)
    | q2Multiply (quat a₀ a₁ a₂ a₃) (quat c₀ c₁ c₂ c₃)
    | q2Multiply (quat b₀ b₁ b₂ b₃) (quat c₀ c₁ c₂ c₃)
    | q3Multiply (quat a₀ a₁ a₂ a₃ +q quat b₀ b₁ b₂ b₃)
      (quat c₀ c₁ c₂ c₃)
    | q3Multiply (quat a₀ a₁ a₂ a₃) (quat c₀ c₁ c₂ c₃)
    | q3Multiply (quat b₀ b₁ b₂ b₃) (quat c₀ c₁ c₂ c₃) =
  quaternionExt
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷
       c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])
      realSolverRing)

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

lieQuaternionAdd :
  ∀ X Y → lieQuaternion (lieAdd X Y) ≡ lieQuaternion X +q lieQuaternion Y
lieQuaternionAdd (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  quaternionExt
    (sym (+-identityˡ zeroR))
    refl
    refl
    refl

quaternionNegate : Quaternion → Quaternion
quaternionNegate (quat a₀ a₁ a₂ a₃) =
  quat (-R a₀) (-R a₁) (-R a₂) (-R a₃)

quaternionScale : ℝ → Quaternion → Quaternion
quaternionScale scalar (quat a₀ a₁ a₂ a₃) =
  quat (scalar *R a₀) (scalar *R a₁) (scalar *R a₂) (scalar *R a₃)

negativeMultiplyLeft : ∀ x y → -R (x *R y) ≡ (-R x) *R y
negativeMultiplyLeft x y =
  DASHI.Physics.YangMills.BalabanRealPolynomialRing.RealRingProperties.-‿distribˡ-* x y

negativeMultiplyRight : ∀ x y → -R (x *R y) ≡ x *R (-R y)
negativeMultiplyRight x y =
  DASHI.Physics.YangMills.BalabanRealPolynomialRing.RealRingProperties.-‿distribʳ-* x y

quaternionMultiplyNegateLeft :
  ∀ a b → quaternionNegate a *q b ≡ quaternionNegate (a *q b)
quaternionMultiplyNegateLeft
  (quat a₀ a₁ a₂ a₃)
  (quat b₀ b₁ b₂ b₃)
  rewrite q0Multiply (quaternionNegate (quat a₀ a₁ a₂ a₃))
    (quat b₀ b₁ b₂ b₃)
    | q0Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q1Multiply (quaternionNegate (quat a₀ a₁ a₂ a₃))
      (quat b₀ b₁ b₂ b₃)
    | q1Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q2Multiply (quaternionNegate (quat a₀ a₁ a₂ a₃))
      (quat b₀ b₁ b₂ b₃)
    | q2Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q3Multiply (quaternionNegate (quat a₀ a₁ a₂ a₃))
      (quat b₀ b₁ b₂ b₃)
    | q3Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | sym (negativeMultiplyLeft a₀ b₀) | sym (negativeMultiplyLeft a₀ b₁)
    | sym (negativeMultiplyLeft a₀ b₂) | sym (negativeMultiplyLeft a₀ b₃)
    | sym (negativeMultiplyLeft a₁ b₀) | sym (negativeMultiplyLeft a₁ b₁)
    | sym (negativeMultiplyLeft a₁ b₂) | sym (negativeMultiplyLeft a₁ b₃)
    | sym (negativeMultiplyLeft a₂ b₀) | sym (negativeMultiplyLeft a₂ b₁)
    | sym (negativeMultiplyLeft a₂ b₂) | sym (negativeMultiplyLeft a₂ b₃)
    | sym (negativeMultiplyLeft a₃ b₀) | sym (negativeMultiplyLeft a₃ b₁)
    | sym (negativeMultiplyLeft a₃ b₂) | sym (negativeMultiplyLeft a₃ b₃) =
  quaternionExt
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) realSolverRing)

quaternionMultiplyNegateRight :
  ∀ a b → a *q quaternionNegate b ≡ quaternionNegate (a *q b)
quaternionMultiplyNegateRight
  (quat a₀ a₁ a₂ a₃)
  (quat b₀ b₁ b₂ b₃)
  rewrite q0Multiply (quat a₀ a₁ a₂ a₃)
    (quaternionNegate (quat b₀ b₁ b₂ b₃))
    | q0Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q1Multiply (quat a₀ a₁ a₂ a₃)
      (quaternionNegate (quat b₀ b₁ b₂ b₃))
    | q1Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q2Multiply (quat a₀ a₁ a₂ a₃)
      (quaternionNegate (quat b₀ b₁ b₂ b₃))
    | q2Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q3Multiply (quat a₀ a₁ a₂ a₃)
      (quaternionNegate (quat b₀ b₁ b₂ b₃))
    | q3Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | sym (negativeMultiplyRight a₀ b₀) | sym (negativeMultiplyRight a₀ b₁)
    | sym (negativeMultiplyRight a₀ b₂) | sym (negativeMultiplyRight a₀ b₃)
    | sym (negativeMultiplyRight a₁ b₀) | sym (negativeMultiplyRight a₁ b₁)
    | sym (negativeMultiplyRight a₁ b₂) | sym (negativeMultiplyRight a₁ b₃)
    | sym (negativeMultiplyRight a₂ b₀) | sym (negativeMultiplyRight a₂ b₁)
    | sym (negativeMultiplyRight a₂ b₂) | sym (negativeMultiplyRight a₂ b₃)
    | sym (negativeMultiplyRight a₃ b₀) | sym (negativeMultiplyRight a₃ b₁)
    | sym (negativeMultiplyRight a₃ b₂) | sym (negativeMultiplyRight a₃ b₃) =
  quaternionExt
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) realSolverRing)

scaleLeft0 : ∀ s a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
  (((s *R a₀) *R b₀ +R (-R ((s *R a₁) *R b₁)))
    +R (-R ((s *R a₂) *R b₂)) +R (-R ((s *R a₃) *R b₃)))
    ≡ s *R (((a₀ *R b₀ +R (-R (a₁ *R b₁))) +R (-R (a₂ *R b₂)) +R (-R (a₃ *R b₃))))
scaleLeft0 = solve 9 (λ s a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
  ((((s :* a₀) :* b₀) :+ (:- ((s :* a₁) :* b₁))) :+ (:- ((s :* a₂) :* b₂)) :+ (:- ((s :* a₃) :* b₃)))
    := s :* (((a₀ :* b₀) :+ (:- (a₁ :* b₁))) :+ (:- (a₂ :* b₂)) :+ (:- (a₃ :* b₃)))) refl

scaleLeft1 : ∀ s a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
  (((s *R a₀) *R b₁ +R ((s *R a₁) *R b₀))
    +R ((s *R a₂) *R b₃) +R (-R ((s *R a₃) *R b₂)))
    ≡ s *R (((a₀ *R b₁ +R (a₁ *R b₀)) +R (a₂ *R b₃) +R (-R (a₃ *R b₂))))
scaleLeft1 = solve 9 (λ s a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
  ((((s :* a₀) :* b₁) :+ ((s :* a₁) :* b₀)) :+ ((s :* a₂) :* b₃) :+ (:- ((s :* a₃) :* b₂)))
    := s :* (((a₀ :* b₁) :+ (a₁ :* b₀)) :+ (a₂ :* b₃) :+ (:- (a₃ :* b₂)))) refl

scaleLeft2 : ∀ s a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
  (((s *R a₀) *R b₂ +R (-R ((s *R a₁) *R b₃)))
    +R ((s *R a₂) *R b₀) +R ((s *R a₃) *R b₁))
    ≡ s *R (((a₀ *R b₂ +R (-R (a₁ *R b₃))) +R (a₂ *R b₀) +R (a₃ *R b₁)))
scaleLeft2 = solve 9 (λ s a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
  ((((s :* a₀) :* b₂) :+ (:- ((s :* a₁) :* b₃))) :+ ((s :* a₂) :* b₀) :+ ((s :* a₃) :* b₁))
    := s :* (((a₀ :* b₂) :+ (:- (a₁ :* b₃))) :+ (a₂ :* b₀) :+ (a₃ :* b₁))) refl

scaleLeft3 : ∀ s a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
  (((s *R a₀) *R b₃ +R ((s *R a₁) *R b₂))
    +R (-R ((s *R a₂) *R b₁)) +R ((s *R a₃) *R b₀))
    ≡ s *R (((a₀ *R b₃ +R (a₁ *R b₂)) +R (-R (a₂ *R b₁)) +R (a₃ *R b₀)))
scaleLeft3 = solve 9 (λ s a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
  ((((s :* a₀) :* b₃) :+ ((s :* a₁) :* b₂)) :+ (:- ((s :* a₂) :* b₁)) :+ ((s :* a₃) :* b₀))
    := s :* (((a₀ :* b₃) :+ (a₁ :* b₂)) :+ (:- (a₂ :* b₁)) :+ (a₃ :* b₀))) refl

quaternionMultiplyScaleLeft :
  ∀ scalar a b → quaternionScale scalar a *q b ≡ quaternionScale scalar (a *q b)
quaternionMultiplyScaleLeft
  scalar
  (quat a₀ a₁ a₂ a₃)
  (quat b₀ b₁ b₂ b₃)
  rewrite q0Multiply (quaternionScale scalar (quat a₀ a₁ a₂ a₃))
    (quat b₀ b₁ b₂ b₃)
    | q0Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q1Multiply (quaternionScale scalar (quat a₀ a₁ a₂ a₃))
      (quat b₀ b₁ b₂ b₃)
    | q1Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q2Multiply (quaternionScale scalar (quat a₀ a₁ a₂ a₃))
      (quat b₀ b₁ b₂ b₃)
    | q2Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q3Multiply (quaternionScale scalar (quat a₀ a₁ a₂ a₃))
      (quat b₀ b₁ b₂ b₃)
    | q3Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃) =
  quaternionExt
    (scaleLeft0 scalar a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
    (scaleLeft1 scalar a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
    (scaleLeft2 scalar a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
    (scaleLeft3 scalar a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)

scaleRight0 = solve 9 (λ s a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
  (((a₀ :* (s :* b₀)) :+ (:- (a₁ :* (s :* b₁)))) :+ (:- (a₂ :* (s :* b₂))) :+ (:- (a₃ :* (s :* b₃))))
    := s :* (((a₀ :* b₀) :+ (:- (a₁ :* b₁))) :+ (:- (a₂ :* b₂)) :+ (:- (a₃ :* b₃)))) refl

scaleRight1 = solve 9 (λ s a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
  (((a₀ :* (s :* b₁)) :+ (a₁ :* (s :* b₀))) :+ (a₂ :* (s :* b₃)) :+ (:- (a₃ :* (s :* b₂))))
    := s :* (((a₀ :* b₁) :+ (a₁ :* b₀)) :+ (a₂ :* b₃) :+ (:- (a₃ :* b₂)))) refl

scaleRight2 = solve 9 (λ s a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
  (((a₀ :* (s :* b₂)) :+ (:- (a₁ :* (s :* b₃)))) :+ (a₂ :* (s :* b₀)) :+ (a₃ :* (s :* b₁)))
    := s :* (((a₀ :* b₂) :+ (:- (a₁ :* b₃))) :+ (a₂ :* b₀) :+ (a₃ :* b₁))) refl

scaleRight3 = solve 9 (λ s a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
  (((a₀ :* (s :* b₃)) :+ (a₁ :* (s :* b₂))) :+ (:- (a₂ :* (s :* b₁))) :+ (a₃ :* (s :* b₀)))
    := s :* (((a₀ :* b₃) :+ (a₁ :* b₂)) :+ (:- (a₂ :* b₁)) :+ (a₃ :* b₀))) refl

quaternionMultiplyScaleRight :
  ∀ scalar a b → a *q quaternionScale scalar b ≡ quaternionScale scalar (a *q b)
quaternionMultiplyScaleRight
  scalar
  (quat a₀ a₁ a₂ a₃)
  (quat b₀ b₁ b₂ b₃)
  rewrite q0Multiply (quat a₀ a₁ a₂ a₃)
    (quaternionScale scalar (quat b₀ b₁ b₂ b₃))
    | q0Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q1Multiply (quat a₀ a₁ a₂ a₃)
      (quaternionScale scalar (quat b₀ b₁ b₂ b₃))
    | q1Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q2Multiply (quat a₀ a₁ a₂ a₃)
      (quaternionScale scalar (quat b₀ b₁ b₂ b₃))
    | q2Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
    | q3Multiply (quat a₀ a₁ a₂ a₃)
      (quaternionScale scalar (quat b₀ b₁ b₂ b₃))
    | q3Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃) =
  quaternionExt
    (scaleRight0 scalar a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
    (scaleRight1 scalar a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
    (scaleRight2 scalar a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
    (scaleRight3 scalar a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)

lieNegate : SU2LieAlgebra → SU2LieAlgebra
lieNegate (su2Lie x y z) = su2Lie (-R x) (-R y) (-R z)

lieSubtract : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
lieSubtract X Y = lieAdd X (lieNegate Y)

lieScale : ℝ → SU2LieAlgebra → SU2LieAlgebra
lieScale scalar (su2Lie x y z) =
  su2Lie (scalar *R x) (scalar *R y) (scalar *R z)

lieQuaternionNegate :
  ∀ X → lieQuaternion (lieNegate X) ≡ quaternionNegate (lieQuaternion X)
lieQuaternionNegate (su2Lie x y z) =
  quaternionExt (sym -0#≈0#) refl refl refl

lieQuaternionScale :
  ∀ scalar X → lieQuaternion (lieScale scalar X) ≡ quaternionScale scalar (lieQuaternion X)
lieQuaternionScale scalar (su2Lie x y z) =
  quaternionExt
    (sym (zeroʳ scalar))
    refl
    refl
    refl

lieScaleZero : ∀ X → lieScale zeroR X ≡ lieZero
lieScaleZero (su2Lie x y z) =
  su2LieExt
    (zeroˡ x)
    (zeroˡ y)
    (zeroˡ z)

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

quaternionConjugateMultiply :
  ∀ a b → conjugateQ (a *q b) ≡ conjugateQ b *q conjugateQ a
quaternionConjugateMultiply a@(quat a₀ a₁ a₂ a₃) b@(quat b₀ b₁ b₂ b₃) =
  quaternionExt
    (conjugateMultiply0 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
    (conjugateMultiply1 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
    (conjugateMultiply2 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
    (conjugateMultiply3 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
  where
  conjugateMultiply0 :
    ∀ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
    q0 (conjugateQ (quat a₀ a₁ a₂ a₃ *q quat b₀ b₁ b₂ b₃))
      ≡ q0 (conjugateQ (quat b₀ b₁ b₂ b₃) *q
        conjugateQ (quat a₀ a₁ a₂ a₃))
  conjugateMultiply0 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
    rewrite q0Conjugate (quat a₀ a₁ a₂ a₃ *q quat b₀ b₁ b₂ b₃)
      | q0Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q0Multiply (conjugateQ (quat b₀ b₁ b₂ b₃))
          (conjugateQ (quat a₀ a₁ a₂ a₃))
      | q0Conjugate (quat b₀ b₁ b₂ b₃)
      | q1Conjugate (quat b₀ b₁ b₂ b₃)
      | q2Conjugate (quat b₀ b₁ b₂ b₃)
      | q3Conjugate (quat b₀ b₁ b₂ b₃)
      | q0Conjugate (quat a₀ a₁ a₂ a₃)
      | q1Conjugate (quat a₀ a₁ a₂ a₃)
      | q2Conjugate (quat a₀ a₁ a₂ a₃)
      | q3Conjugate (quat a₀ a₁ a₂ a₃)
      | [-x][-y]≈xy b₁ a₁
      | [-x][-y]≈xy b₂ a₂
      | [-x][-y]≈xy b₃ a₃ =
    Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ [])
      realSolverRing

  conjugateMultiply1 :
    ∀ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
    q1 (conjugateQ (quat a₀ a₁ a₂ a₃ *q quat b₀ b₁ b₂ b₃))
      ≡ q1 (conjugateQ (quat b₀ b₁ b₂ b₃) *q
        conjugateQ (quat a₀ a₁ a₂ a₃))
  conjugateMultiply1 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
    rewrite q1Conjugate (quat a₀ a₁ a₂ a₃ *q quat b₀ b₁ b₂ b₃)
      | q0Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q1Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q2Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q3Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q1Multiply (conjugateQ (quat b₀ b₁ b₂ b₃))
          (conjugateQ (quat a₀ a₁ a₂ a₃))
      | q0Conjugate (quat b₀ b₁ b₂ b₃)
      | q1Conjugate (quat b₀ b₁ b₂ b₃)
      | q2Conjugate (quat b₀ b₁ b₂ b₃)
      | q3Conjugate (quat b₀ b₁ b₂ b₃)
      | q0Conjugate (quat a₀ a₁ a₂ a₃)
      | q1Conjugate (quat a₀ a₁ a₂ a₃)
      | q2Conjugate (quat a₀ a₁ a₂ a₃)
      | q3Conjugate (quat a₀ a₁ a₂ a₃)
      = conjugateProduct1Polynomial a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃

  conjugateMultiply2 :
    ∀ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
    q2 (conjugateQ (quat a₀ a₁ a₂ a₃ *q quat b₀ b₁ b₂ b₃))
      ≡ q2 (conjugateQ (quat b₀ b₁ b₂ b₃) *q
        conjugateQ (quat a₀ a₁ a₂ a₃))
  conjugateMultiply2 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
    rewrite q2Conjugate (quat a₀ a₁ a₂ a₃ *q quat b₀ b₁ b₂ b₃)
      | q0Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q1Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q2Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q3Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q2Multiply (conjugateQ (quat b₀ b₁ b₂ b₃))
          (conjugateQ (quat a₀ a₁ a₂ a₃))
      | q0Conjugate (quat b₀ b₁ b₂ b₃)
      | q1Conjugate (quat b₀ b₁ b₂ b₃)
      | q2Conjugate (quat b₀ b₁ b₂ b₃)
      | q3Conjugate (quat b₀ b₁ b₂ b₃)
      | q0Conjugate (quat a₀ a₁ a₂ a₃)
      | q1Conjugate (quat a₀ a₁ a₂ a₃)
      | q2Conjugate (quat a₀ a₁ a₂ a₃)
      | q3Conjugate (quat a₀ a₁ a₂ a₃) =
    conjugateProduct2Polynomial a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃

  conjugateMultiply3 :
    ∀ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
    q3 (conjugateQ (quat a₀ a₁ a₂ a₃ *q quat b₀ b₁ b₂ b₃))
      ≡ q3 (conjugateQ (quat b₀ b₁ b₂ b₃) *q
        conjugateQ (quat a₀ a₁ a₂ a₃))
  conjugateMultiply3 a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
    rewrite q3Conjugate (quat a₀ a₁ a₂ a₃ *q quat b₀ b₁ b₂ b₃)
      | q0Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q1Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q2Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q3Multiply (quat a₀ a₁ a₂ a₃) (quat b₀ b₁ b₂ b₃)
      | q3Multiply (conjugateQ (quat b₀ b₁ b₂ b₃))
          (conjugateQ (quat a₀ a₁ a₂ a₃))
      | q0Conjugate (quat b₀ b₁ b₂ b₃)
      | q1Conjugate (quat b₀ b₁ b₂ b₃)
      | q2Conjugate (quat b₀ b₁ b₂ b₃)
      | q3Conjugate (quat b₀ b₁ b₂ b₃)
      | q0Conjugate (quat a₀ a₁ a₂ a₃)
      | q1Conjugate (quat a₀ a₁ a₂ a₃)
      | q2Conjugate (quat a₀ a₁ a₂ a₃)
      | q3Conjugate (quat a₀ a₁ a₂ a₃) =
    conjugateProduct3Polynomial a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃

adjointQuaternionMultiply :
  ∀ a b X →
  ((a *q b) *q X) *q conjugateQ (a *q b)
    ≡ a *q (b *q X) *q conjugateQ b *q conjugateQ a
adjointQuaternionMultiply a b X =
  trans
    (cong (λ q → q *q conjugateQ (a *q b))
      (quaternionMultiplyAssociative a b X))
    (trans
      (cong (λ q → (a *q (b *q X)) *q q)
        (quaternionConjugateMultiply a b))
      (sym (quaternionMultiplyAssociative
        (a *q (b *q X)) (conjugateQ b) (conjugateQ a))))

adjointQuaternionNested :
  ∀ u v X →
  adjointQuaternion u (su2Adjoint v X)
    ≡ (quaternion u *q adjointQuaternion v X)
      *q conjugateQ (quaternion u)
adjointQuaternionNested u v X =
  cong
    (λ q → (quaternion u *q q) *q conjugateQ (quaternion u))
    (lieQuaternionAdjoint v X)

adjointQuaternionMultiplyNested :
  ∀ u v X →
  adjointQuaternion (su2Multiply u v) X
    ≡ adjointQuaternion u (su2Adjoint v X)
adjointQuaternionMultiplyNested u v X =
  trans
    (adjointQuaternionMultiply
      (quaternion u)
      (quaternion v)
      (lieQuaternion X))
    (trans
      (cong
        (λ q → q *q conjugateQ (quaternion u))
        (quaternionMultiplyAssociative
          (quaternion u)
          (quaternion v *q lieQuaternion X)
          (conjugateQ (quaternion v))))
      (sym (adjointQuaternionNested u v X)))

adjointQuaternionAdd :
  ∀ u X Y →
  adjointQuaternion u (lieAdd X Y)
    ≡ adjointQuaternion u X +q adjointQuaternion u Y
adjointQuaternionAdd u X Y =
  trans
    (cong
      (λ q → (quaternion u *q q) *q conjugateQ (quaternion u))
      (lieQuaternionAdd X Y))
    (trans
      (cong (λ q → q *q conjugateQ (quaternion u))
        (quaternionMultiplyAddLeft
          (quaternion u)
          (lieQuaternion X)
          (lieQuaternion Y)))
      (quaternionMultiplyAddRight
        (quaternion u *q lieQuaternion X)
        (quaternion u *q lieQuaternion Y)
        (conjugateQ (quaternion u))))

adjointQuaternionNegate :
  ∀ u X →
  adjointQuaternion u (lieNegate X)
    ≡ quaternionNegate (adjointQuaternion u X)
adjointQuaternionNegate u X =
  trans
    (cong
      (λ q → (quaternion u *q q) *q conjugateQ (quaternion u))
      (lieQuaternionNegate X))
    (trans
      (cong (λ q → q *q conjugateQ (quaternion u))
        (quaternionMultiplyNegateRight
          (quaternion u)
          (lieQuaternion X)))
      (quaternionMultiplyNegateLeft
        (quaternion u *q lieQuaternion X)
        (conjugateQ (quaternion u))))

adjointQuaternionScale :
  ∀ u scalar X →
  adjointQuaternion u (lieScale scalar X)
    ≡ quaternionScale scalar (adjointQuaternion u X)
adjointQuaternionScale u scalar X =
  trans
    (cong
      (λ q → (quaternion u *q q) *q conjugateQ (quaternion u))
      (lieQuaternionScale scalar X))
    (trans
      (cong (λ q → q *q conjugateQ (quaternion u))
        (quaternionMultiplyScaleRight
          scalar
          (quaternion u)
          (lieQuaternion X)))
      (quaternionMultiplyScaleLeft
        scalar
        (quaternion u *q lieQuaternion X)
        (conjugateQ (quaternion u))))

su2AdjointNegate :
  ∀ u X → su2Adjoint u (lieNegate X) ≡ lieNegate (su2Adjoint u X)
su2AdjointNegate u X =
  su2LieExt
    (trans
      (cong q1 (adjointQuaternionNegate u X))
      (sym (cong q1 (lieQuaternionNegate (su2Adjoint u X)))))
    (trans
      (cong q2 (adjointQuaternionNegate u X))
      (sym (cong q2 (lieQuaternionNegate (su2Adjoint u X)))))
    (trans
      (cong q3 (adjointQuaternionNegate u X))
      (sym (cong q3 (lieQuaternionNegate (su2Adjoint u X)))))

su2AdjointScaleBridge :
  ∀ u scalar X →
  su2Adjoint u (lieScale scalar X) ≡ lieScale scalar (su2Adjoint u X)
su2AdjointScaleBridge u scalar X =
  su2LieExt
    (trans
      (cong q1 (adjointQuaternionScale u scalar X))
      (sym (cong q1 (lieQuaternionScale scalar (su2Adjoint u X)))))
    (trans
      (cong q2 (adjointQuaternionScale u scalar X))
      (sym (cong q2 (lieQuaternionScale scalar (su2Adjoint u X)))))
    (trans
      (cong q3 (adjointQuaternionScale u scalar X))
      (sym (cong q3 (lieQuaternionScale scalar (su2Adjoint u X)))))

su2AdjointMultiply :
  ∀ u v X →
  su2Adjoint (su2Multiply u v) X
    ≡ su2Adjoint u (su2Adjoint v X)
su2AdjointMultiply
  (su2q (quat a₀ a₁ a₂ a₃) a-unit)
  (su2q (quat b₀ b₁ b₂ b₃) b-unit)
  (su2Lie x y z) =
  let proof = adjointQuaternionMultiplyNested
        (su2q (quat a₀ a₁ a₂ a₃) a-unit)
        (su2q (quat b₀ b₁ b₂ b₃) b-unit)
        (su2Lie x y z)
  in su2LieExt
    (cong q1 proof)
    (cong q2 proof)
    (cong q3 proof)


su2AdjointAdd :
  ∀ u X Y →
  su2Adjoint u (lieAdd X Y)
    ≡ lieAdd (su2Adjoint u X) (su2Adjoint u Y)
su2AdjointAdd
  (su2q (quat a₀ a₁ a₂ a₃) a-unit)
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂) =
  su2LieExt
    (trans
      (cong q1
        (adjointQuaternionAdd
          (su2q (quat a₀ a₁ a₂ a₃) a-unit)
          (su2Lie x₁ y₁ z₁)
          (su2Lie x₂ y₂ z₂)))
      (sym (cong q1
        (lieQuaternionAdd
          (su2Adjoint (su2q (quat a₀ a₁ a₂ a₃) a-unit)
            (su2Lie x₁ y₁ z₁))
          (su2Adjoint (su2q (quat a₀ a₁ a₂ a₃) a-unit)
            (su2Lie x₂ y₂ z₂))))))
    (trans
      (cong q2
        (adjointQuaternionAdd
          (su2q (quat a₀ a₁ a₂ a₃) a-unit)
          (su2Lie x₁ y₁ z₁)
          (su2Lie x₂ y₂ z₂)))
      (sym (cong q2
        (lieQuaternionAdd
          (su2Adjoint (su2q (quat a₀ a₁ a₂ a₃) a-unit)
            (su2Lie x₁ y₁ z₁))
          (su2Adjoint (su2q (quat a₀ a₁ a₂ a₃) a-unit)
            (su2Lie x₂ y₂ z₂))))))
    (trans
      (cong q3
        (adjointQuaternionAdd
          (su2q (quat a₀ a₁ a₂ a₃) a-unit)
          (su2Lie x₁ y₁ z₁)
          (su2Lie x₂ y₂ z₂)))
      (sym (cong q3
        (lieQuaternionAdd
          (su2Adjoint (su2q (quat a₀ a₁ a₂ a₃) a-unit)
            (su2Lie x₁ y₁ z₁))
          (su2Adjoint (su2q (quat a₀ a₁ a₂ a₃) a-unit)
            (su2Lie x₂ y₂ z₂))))))

su2AdjointSubtract :
  ∀ u X Y →
  su2Adjoint u (lieSubtract X Y)
    ≡ lieSubtract (su2Adjoint u X) (su2Adjoint u Y)
su2AdjointSubtract
  u X Y =
  trans
    (su2AdjointAdd u X (lieNegate Y))
    (cong (lieAdd (su2Adjoint u X)) (su2AdjointNegate u Y))

su2AdjointZero : ∀ u → su2Adjoint u lieZero ≡ lieZero
su2AdjointZero u =
  trans
    (cong (su2Adjoint u) (sym (lieScaleZero lieZero)))
    (trans
      (su2AdjointScaleBridge u zeroR lieZero)
      (lieScaleZero (su2Adjoint u lieZero)))

su2AdjointScale :
  ∀ u scalar X →
  su2Adjoint u (lieScale scalar X)
    ≡ lieScale scalar (su2Adjoint u X)
su2AdjointScale
  u scalar X = su2AdjointScaleBridge u scalar X

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
