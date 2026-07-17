module DASHI.Physics.YangMills.BalabanSU2ReducedAdjointGaugeCovariance where

------------------------------------------------------------------------
-- Gauge covariance of the concrete adjoint functional calculus.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Tactic.RingSolver as Solver

open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( quat
  ; _*R_
  ; -R_
  ; realSolverRing
  ; su2q
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( su2Lie
  ; su2LieExt
  ; su2Adjoint
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  ( su2DotAdjointInvariant )
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  ( lieBracket )
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  ( fourR
  ; adCubicCoefficient
  )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( reducedAd
  ; applyReducedAdjoint
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointMatrixDeterminant using
  ( determinantMatrix3
  ; reducedAdjointMatrix
  ; reducedAdjointDeterminant
  )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointDeterminantProduct using
  ( reducedAdjointDeterminantValue )

su2AdjointBracketEquivariant :
  ∀ u Y X →
  su2Adjoint u (lieBracket Y X)
    ≡ lieBracket (su2Adjoint u Y) (su2Adjoint u X)
su2AdjointBracketEquivariant
  (su2q (quat a₀ a₁ a₂ a₃) unit)
  (su2Lie y₁ y₂ y₃)
  (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ y₁ ∷ y₂ ∷ y₃ ∷
       x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ y₁ ∷ y₂ ∷ y₃ ∷
       x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ y₁ ∷ y₂ ∷ y₃ ∷
       x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)

applyReducedAdjointGaugeCovariant :
  ∀ u Y operator X →
  su2Adjoint u (applyReducedAdjoint Y operator X)
  ≡
  applyReducedAdjoint
    (su2Adjoint u Y)
    operator
    (su2Adjoint u X)
applyReducedAdjointGaugeCovariant
  (su2q (quat a₀ a₁ a₂ a₃) unit)
  (su2Lie y₁ y₂ y₃)
  (reducedAd α β γ)
  (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ y₁ ∷ y₂ ∷ y₃ ∷
       α ∷ β ∷ γ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ y₁ ∷ y₂ ∷ y₃ ∷
       α ∷ β ∷ γ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ y₁ ∷ y₂ ∷ y₃ ∷
       α ∷ β ∷ γ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)

adCubicCoefficientGaugeInvariant :
  ∀ u Y →
  adCubicCoefficient (su2Adjoint u Y)
    ≡ adCubicCoefficient Y
adCubicCoefficientGaugeInvariant u Y =
  cong
    (λ norm → -R (fourR *R norm))
    (su2DotAdjointInvariant u Y Y)

reducedAdjointDeterminantGaugeInvariant :
  ∀ u Y operator →
  reducedAdjointDeterminantValue
    (su2Adjoint u Y) operator
  ≡ reducedAdjointDeterminantValue Y operator
reducedAdjointDeterminantGaugeInvariant
  u Y (reducedAd a b c)
  rewrite adCubicCoefficientGaugeInvariant u Y = refl

reducedAdjointMatrixDeterminantGaugeInvariant :
  ∀ u Y operator →
  determinantMatrix3
    (reducedAdjointMatrix (su2Adjoint u Y) operator)
  ≡
  determinantMatrix3
    (reducedAdjointMatrix Y operator)
reducedAdjointMatrixDeterminantGaugeInvariant
  u Y (reducedAd a b c) =
  trans
    (reducedAdjointDeterminant (su2Adjoint u Y) a b c)
    (trans
      (reducedAdjointDeterminantGaugeInvariant
        u Y (reducedAd a b c))
      (sym (reducedAdjointDeterminant Y a b c)))
