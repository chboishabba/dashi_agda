module DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct where

------------------------------------------------------------------------
-- Concrete invariant inner product and scalar module on su(2).
--
-- The Euclidean dot product on the three imaginary quaternion coordinates is
-- invariant under conjugation by a unit quaternion.  The large ten-variable
-- polynomial is deliberately discharged through DASHI's integer-coefficient
-- polynomial socket rather than the stdlib reflective RingSolver: the latter
-- cannot see the axiomatic real aliases definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( AdjointLinearModule )
open import DASHI.Physics.YangMills.BalabanLinearBlockPathAverage using
  ( ScalarAdjointLinearModule )
open import DASHI.Physics.YangMills.BalabanFiniteAdjointQuadraticForms using
  ( AdjointInnerProductModule )
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver )
open RealPolynomialSolver using
  ( Polynomial; solve; _:=_; _:+_; _:*_; :-_ )
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  ( q1R; q2R; q3R; q1P; q2P; q3P )
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
  ; oneR
  ; normSquaredQ
  ; normSquaredExpand
  ; realSolverRing
  ; q1Multiply
  ; q2Multiply
  ; q3Multiply
  ; q0Conjugate
  ; q1Conjugate
  ; q2Conjugate
  ; q3Conjugate
  ; SU2Quaternion
  ; su2q
  ; quaternion
  ; unitNormSquared
  ; su2QuaternionGroup
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; xComponent
  ; yComponent
  ; zComponent
  ; lieScale
  ; lieQuaternion
  ; adjointInner0
  ; adjointInner1
  ; adjointInner2
  ; adjointInner3
  ; su2Adjoint
  ; su2AdjointScale
  ; su2AdjointLinearModule
  )

su2Dot : SU2LieAlgebra → SU2LieAlgebra → ℝ
su2Dot (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  ((x₁ *R x₂) +R (y₁ *R y₂)) +R (z₁ *R z₂)

private
  inner0R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  inner0R a₀ a₁ a₂ a₃ x y z =
    ((-R (a₁ *R x)) +R (-R (a₂ *R y))) +R (-R (a₃ *R z))

  inner1R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  inner1R a₀ a₁ a₂ a₃ x y z =
    ((a₀ *R x) +R (a₂ *R z)) +R (-R (a₃ *R y))

  inner2R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  inner2R a₀ a₁ a₂ a₃ x y z =
    ((a₀ *R y) +R (-R (a₁ *R z))) +R (a₃ *R x)

  inner3R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  inner3R a₀ a₁ a₂ a₃ x y z =
    ((a₀ *R z) +R (a₁ *R y)) +R (-R (a₂ *R x))

  inner0P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
    Polynomial n → Polynomial n → Polynomial n → Polynomial n
  inner0P a₀ a₁ a₂ a₃ x y z =
    (((:- (a₁ :* x)) :+ (:- (a₂ :* y))) :+ (:- (a₃ :* z)))

  inner1P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
    Polynomial n → Polynomial n → Polynomial n → Polynomial n
  inner1P a₀ a₁ a₂ a₃ x y z =
    (((a₀ :* x) :+ (a₂ :* z)) :+ (:- (a₃ :* y)))

  inner2P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
    Polynomial n → Polynomial n → Polynomial n → Polynomial n
  inner2P a₀ a₁ a₂ a₃ x y z =
    (((a₀ :* y) :+ (:- (a₁ :* z))) :+ (a₃ :* x))

  inner3P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
    Polynomial n → Polynomial n → Polynomial n → Polynomial n
  inner3P a₀ a₁ a₂ a₃ x y z =
    (((a₀ :* z) :+ (a₁ :* y)) :+ (:- (a₂ :* x)))

  adj1R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  adj1R a₀ a₁ a₂ a₃ x y z =
    q1R
      (inner0R a₀ a₁ a₂ a₃ x y z)
      (inner1R a₀ a₁ a₂ a₃ x y z)
      (inner2R a₀ a₁ a₂ a₃ x y z)
      (inner3R a₀ a₁ a₂ a₃ x y z)
      a₀ (-R a₁) (-R a₂) (-R a₃)

  adj2R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  adj2R a₀ a₁ a₂ a₃ x y z =
    q2R
      (inner0R a₀ a₁ a₂ a₃ x y z)
      (inner1R a₀ a₁ a₂ a₃ x y z)
      (inner2R a₀ a₁ a₂ a₃ x y z)
      (inner3R a₀ a₁ a₂ a₃ x y z)
      a₀ (-R a₁) (-R a₂) (-R a₃)

  adj3R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  adj3R a₀ a₁ a₂ a₃ x y z =
    q3R
      (inner0R a₀ a₁ a₂ a₃ x y z)
      (inner1R a₀ a₁ a₂ a₃ x y z)
      (inner2R a₀ a₁ a₂ a₃ x y z)
      (inner3R a₀ a₁ a₂ a₃ x y z)
      a₀ (-R a₁) (-R a₂) (-R a₃)

  adj1P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
    Polynomial n → Polynomial n → Polynomial n → Polynomial n
  adj1P a₀ a₁ a₂ a₃ x y z =
    q1P
      (inner0P a₀ a₁ a₂ a₃ x y z)
      (inner1P a₀ a₁ a₂ a₃ x y z)
      (inner2P a₀ a₁ a₂ a₃ x y z)
      (inner3P a₀ a₁ a₂ a₃ x y z)
      a₀ (:- a₁) (:- a₂) (:- a₃)

  adj2P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
    Polynomial n → Polynomial n → Polynomial n → Polynomial n
  adj2P a₀ a₁ a₂ a₃ x y z =
    q2P
      (inner0P a₀ a₁ a₂ a₃ x y z)
      (inner1P a₀ a₁ a₂ a₃ x y z)
      (inner2P a₀ a₁ a₂ a₃ x y z)
      (inner3P a₀ a₁ a₂ a₃ x y z)
      a₀ (:- a₁) (:- a₂) (:- a₃)

  adj3P : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
    Polynomial n → Polynomial n → Polynomial n → Polynomial n
  adj3P a₀ a₁ a₂ a₃ x y z =
    q3P
      (inner0P a₀ a₁ a₂ a₃ x y z)
      (inner1P a₀ a₁ a₂ a₃ x y z)
      (inner2P a₀ a₁ a₂ a₃ x y z)
      (inner3P a₀ a₁ a₂ a₃ x y z)
      a₀ (:- a₁) (:- a₂) (:- a₃)

adjointDotNormFactorPolynomial :
  ∀ a₀ a₁ a₂ a₃ x₁ y₁ z₁ x₂ y₂ z₂ →
  ((adj1R a₀ a₁ a₂ a₃ x₁ y₁ z₁ *R adj1R a₀ a₁ a₂ a₃ x₂ y₂ z₂)
    +R (adj2R a₀ a₁ a₂ a₃ x₁ y₁ z₁ *R adj2R a₀ a₁ a₂ a₃ x₂ y₂ z₂))
    +R (adj3R a₀ a₁ a₂ a₃ x₁ y₁ z₁ *R adj3R a₀ a₁ a₂ a₃ x₂ y₂ z₂)
  ≡
  (((((a₀ *R a₀) +R (a₁ *R a₁)) +R (a₂ *R a₂)) +R (a₃ *R a₃))
    *R ((((a₀ *R a₀) +R (a₁ *R a₁)) +R (a₂ *R a₂)) +R (a₃ *R a₃)))
    *R (((x₁ *R x₂) +R (y₁ *R y₂)) +R (z₁ *R z₂))
adjointDotNormFactorPolynomial =
  solve 10
    (λ a₀ a₁ a₂ a₃ x₁ y₁ z₁ x₂ y₂ z₂ →
      (((adj1P a₀ a₁ a₂ a₃ x₁ y₁ z₁ :* adj1P a₀ a₁ a₂ a₃ x₂ y₂ z₂)
        :+ (adj2P a₀ a₁ a₂ a₃ x₁ y₁ z₁ :* adj2P a₀ a₁ a₂ a₃ x₂ y₂ z₂))
        :+ (adj3P a₀ a₁ a₂ a₃ x₁ y₁ z₁ :* adj3P a₀ a₁ a₂ a₃ x₂ y₂ z₂))
      :=
      (((((a₀ :* a₀) :+ (a₁ :* a₁)) :+ (a₂ :* a₂)) :+ (a₃ :* a₃))
        :* ((((a₀ :* a₀) :+ (a₁ :* a₁)) :+ (a₂ :* a₂)) :+ (a₃ :* a₃)))
        :* (((x₁ :* x₂) :+ (y₁ :* y₂)) :+ (z₁ :* z₂)))
    refl

adjointDotNormFactor :
  ∀ u X Y →
  su2Dot (su2Adjoint u X) (su2Adjoint u Y)
    ≡
  (normSquaredQ (quaternion u) *R normSquaredQ (quaternion u))
    *R su2Dot X Y
adjointDotNormFactor
  (su2q q@(quat a₀ a₁ a₂ a₃) a-unit)
  (su2Lie x₁ y₁ z₁)
  (su2Lie x₂ y₂ z₂)
  rewrite q1Multiply (q *q lieQuaternion (su2Lie x₁ y₁ z₁)) (conjugateQ q)
        | q2Multiply (q *q lieQuaternion (su2Lie x₁ y₁ z₁)) (conjugateQ q)
        | q3Multiply (q *q lieQuaternion (su2Lie x₁ y₁ z₁)) (conjugateQ q)
        | q1Multiply (q *q lieQuaternion (su2Lie x₂ y₂ z₂)) (conjugateQ q)
        | q2Multiply (q *q lieQuaternion (su2Lie x₂ y₂ z₂)) (conjugateQ q)
        | q3Multiply (q *q lieQuaternion (su2Lie x₂ y₂ z₂)) (conjugateQ q)
        | adjointInner0 a₀ a₁ a₂ a₃ x₁ y₁ z₁
        | adjointInner1 a₀ a₁ a₂ a₃ x₁ y₁ z₁
        | adjointInner2 a₀ a₁ a₂ a₃ x₁ y₁ z₁
        | adjointInner3 a₀ a₁ a₂ a₃ x₁ y₁ z₁
        | adjointInner0 a₀ a₁ a₂ a₃ x₂ y₂ z₂
        | adjointInner1 a₀ a₁ a₂ a₃ x₂ y₂ z₂
        | adjointInner2 a₀ a₁ a₂ a₃ x₂ y₂ z₂
        | adjointInner3 a₀ a₁ a₂ a₃ x₂ y₂ z₂
        | q0Conjugate q | q1Conjugate q | q2Conjugate q | q3Conjugate q
        | normSquaredExpand q =
  adjointDotNormFactorPolynomial a₀ a₁ a₂ a₃ x₁ y₁ z₁ x₂ y₂ z₂

su2DotAdjointInvariant :
  ∀ u X Y →
  su2Dot (su2Adjoint u X) (su2Adjoint u Y) ≡ su2Dot X Y
su2DotAdjointInvariant u X Y =
  trans
    (adjointDotNormFactor u X Y)
    (trans
      (cong
        (λ norm → (norm *R norm) *R su2Dot X Y)
        (unitNormSquared u))
      (Solver.solve
        (su2Dot X Y ∷ [])
        realSolverRing))
  where
  open import Data.List.Base using ([]; _∷_)

su2ScaleActionCommutes :
  ∀ u scalar X →
  su2Adjoint u (lieScale scalar X)
    ≡ lieScale scalar (su2Adjoint u X)
su2ScaleActionCommutes = su2AdjointScale

su2ScalarAdjointLinearModule :
  ScalarAdjointLinearModule su2QuaternionGroup
su2ScalarAdjointLinearModule = record
  { linear = su2AdjointLinearModule
  ; Scalar = ℝ
  ; scale = lieScale
  ; actionScale = su2ScaleActionCommutes
  }

su2AdjointInnerProductModule :
  AdjointInnerProductModule su2QuaternionGroup
su2AdjointInnerProductModule = record
  { linear = su2AdjointLinearModule
  ; Scalar = ℝ
  ; zeroScalar = zeroR
  ; addScalar = _+R_
  ; inner = su2Dot
  ; innerActionInvariant = su2DotAdjointInvariant
  }
