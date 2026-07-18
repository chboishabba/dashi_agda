module DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct where

------------------------------------------------------------------------
-- Concrete invariant inner product and scalar module on su(2).
--
-- The Euclidean dot product on the three imaginary quaternion coordinates is
-- invariant under conjugation by a unit quaternion.  The polynomial part is
-- proved first with the exact norm-squared factor; the unit-norm witness then
-- removes that factor.  This instantiates the finite quadratic-form and block
-- average interfaces used by the literal Bałaban lane.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( AdjointLinearModule )
open import DASHI.Physics.YangMills.BalabanLinearBlockPathAverage using
  ( ScalarAdjointLinearModule )
open import DASHI.Physics.YangMills.BalabanFiniteAdjointQuadraticForms using
  ( AdjointInnerProductModule )
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
  ; su2Adjoint
  ; su2AdjointScale
  ; su2AdjointLinearModule
  )

su2Dot : SU2LieAlgebra → SU2LieAlgebra → ℝ
su2Dot (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  ((x₁ *R x₂) +R (y₁ *R y₂)) +R (z₁ *R z₂)

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
  rewrite normSquaredExpand q =
  Solver.solve
    (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷
     x₁ ∷ y₁ ∷ z₁ ∷ x₂ ∷ y₂ ∷ z₂ ∷ [])
    realSolverRing

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
