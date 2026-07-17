module DASHI.Physics.YangMills.BalabanSU2ReducedAdjointGaugeCovariance where

------------------------------------------------------------------------
-- Gauge covariance of the concrete adjoint functional calculus.
--
-- For a general quaternion q, conjugation satisfies
--
--   [qYq*,qXq*] = |q|² q[Y,X]q*.
--
-- The SU(2) unit-norm witness removes the factor.  Reduced-operator covariance
-- is then proved structurally from bracket equivariance and linearity rather
-- than asking the polynomial solver to use an erased unit-norm premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  ( cong; cong₂; sym; trans )

import Tactic.RingSolver as Solver

open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( quat
  ; _*R_
  ; -R_
  ; oneR
  ; normSquaredQ
  ; realSolverRing
  ; su2q
  ; quaternion
  ; unitNormSquared
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; lieAdd
  ; lieScale
  ; su2Adjoint
  ; su2AdjointAdd
  ; su2AdjointScale
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

lieScaleOne :
  ∀ X → lieScale oneR X ≡ X
lieScaleOne (su2Lie x y z) =
  su2LieExt
    (Solver.solve (x ∷ []) realSolverRing)
    (Solver.solve (y ∷ []) realSolverRing)
    (Solver.solve (z ∷ []) realSolverRing)

su2AdjointBracketNormFactor :
  ∀ u Y X →
  lieBracket (su2Adjoint u Y) (su2Adjoint u X)
  ≡
  lieScale
    (normSquaredQ (quaternion u))
    (su2Adjoint u (lieBracket Y X))
su2AdjointBracketNormFactor
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

su2AdjointBracketEquivariant :
  ∀ u Y X →
  su2Adjoint u (lieBracket Y X)
    ≡ lieBracket (su2Adjoint u Y) (su2Adjoint u X)
su2AdjointBracketEquivariant u Y X =
  trans
    (sym (lieScaleOne (su2Adjoint u (lieBracket Y X))))
    (trans
      (cong
        (λ scalar → lieScale scalar (su2Adjoint u (lieBracket Y X)))
        (sym (unitNormSquared u)))
      (sym (su2AdjointBracketNormFactor u Y X)))

su2AdjointAdSquaredEquivariant :
  ∀ u Y X →
  su2Adjoint u (lieBracket Y (lieBracket Y X))
  ≡
  lieBracket
    (su2Adjoint u Y)
    (lieBracket (su2Adjoint u Y) (su2Adjoint u X))
su2AdjointAdSquaredEquivariant u Y X =
  trans
    (su2AdjointBracketEquivariant u Y (lieBracket Y X))
    (cong
      (lieBracket (su2Adjoint u Y))
      (su2AdjointBracketEquivariant u Y X))

applyReducedAdjointGaugeCovariant :
  ∀ u Y operator X →
  su2Adjoint u (applyReducedAdjoint Y operator X)
  ≡
  applyReducedAdjoint
    (su2Adjoint u Y)
    operator
    (su2Adjoint u X)
applyReducedAdjointGaugeCovariant
  u Y (reducedAd a b c) X =
  trans
    (su2AdjointAdd u
      (lieScale a X)
      (lieAdd
        (lieScale b (lieBracket Y X))
        (lieScale c (lieBracket Y (lieBracket Y X)))))
    (cong₂ lieAdd
      (su2AdjointScale u a X)
      (trans
        (su2AdjointAdd u
          (lieScale b (lieBracket Y X))
          (lieScale c (lieBracket Y (lieBracket Y X))))
        (cong₂ lieAdd
          (trans
            (su2AdjointScale u b (lieBracket Y X))
            (cong (lieScale b)
              (su2AdjointBracketEquivariant u Y X)))
          (trans
            (su2AdjointScale u c
              (lieBracket Y (lieBracket Y X)))
            (cong (lieScale c)
              (su2AdjointAdSquaredEquivariant u Y X))))))

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
