module DASHI.Physics.YangMills.BalabanSU2ReducedAdjointAdjugate where

------------------------------------------------------------------------
-- Polynomial adjugate in the reduced su(2) adjoint algebra.
--
-- For P = a I + b A + c A^2 and A^3 = k A, define
--
--   adj(P) = p I + q A + r A^2
--
-- with
--
--   p = a^2 + 2ack - b^2k + c^2k^2,
--   q = -ab,
--   r = b^2 - ac - c^2k.
--
-- Then
--
--   P adj(P) = det(P) I.
--
-- This gives the exact numerator of the inverse without assuming division or
-- non-vanishing of the determinant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_
  ; _*R_
  ; -R_
  ; zeroR
  ; oneR
  ; realSolverRing
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; lieScale
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  ( adCubicCoefficient )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( ReducedAdjointOperator
  ; reducedAd
  ; identityCoefficient
  ; linearCoefficient
  ; quadraticCoefficient
  ; applyReducedAdjoint
  ; composeReducedAdjoint
  ; applyReducedComposition
  )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointDeterminantProduct using
  ( reducedAdjointDeterminantValue )

twoR : ℝ
twoR = oneR +R oneR

scaleIdentityReduced : ℝ → ReducedAdjointOperator
scaleIdentityReduced scalar = reducedAd scalar zeroR zeroR

reducedAdjointAdjugate :
  SU2LieAlgebra →
  ReducedAdjointOperator →
  ReducedAdjointOperator
reducedAdjointAdjugate Y (reducedAd a b c) =
  reducedAd
    ((((a *R a) +R (twoR *R ((a *R c) *R k)))
      +R (-R ((b *R b) *R k)))
      +R ((c *R c) *R (k *R k)))
    (-R (a *R b))
    (((b *R b) +R (-R (a *R c)))
      +R (-R ((c *R c) *R k)))
  where
    k : ℝ
    k = adCubicCoefficient Y

reducedAdjointAdjugateProduct :
  ∀ Y operator →
  composeReducedAdjoint Y operator
    (reducedAdjointAdjugate Y operator)
  ≡
  scaleIdentityReduced
    (reducedAdjointDeterminantValue Y operator)
reducedAdjointAdjugateProduct Y (reducedAd a b c) =
  DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus.reducedAdjointExt
    (Solver.solve
      (a ∷ b ∷ c ∷ adCubicCoefficient Y ∷ []) realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ adCubicCoefficient Y ∷ []) realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ adCubicCoefficient Y ∷ []) realSolverRing)

reducedAdjointAdjugateProductRight :
  ∀ Y operator →
  composeReducedAdjoint Y
    (reducedAdjointAdjugate Y operator)
    operator
  ≡
  scaleIdentityReduced
    (reducedAdjointDeterminantValue Y operator)
reducedAdjointAdjugateProductRight Y (reducedAd a b c) =
  DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus.reducedAdjointExt
    (Solver.solve
      (a ∷ b ∷ c ∷ adCubicCoefficient Y ∷ []) realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ adCubicCoefficient Y ∷ []) realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ adCubicCoefficient Y ∷ []) realSolverRing)

applyScaleIdentityReduced :
  ∀ Y scalar X →
  applyReducedAdjoint Y (scaleIdentityReduced scalar) X
    ≡ lieScale scalar X
applyScaleIdentityReduced Y scalar (su2Lie x y z) =
  su2LieExt
    (Solver.solve (scalar ∷ x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve (scalar ∷ x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve (scalar ∷ x ∷ y ∷ z ∷ []) realSolverRing)

applyReducedAdjugateProduct :
  ∀ Y operator X →
  applyReducedAdjoint Y operator
    (applyReducedAdjoint Y
      (reducedAdjointAdjugate Y operator) X)
  ≡
  lieScale
    (reducedAdjointDeterminantValue Y operator)
    X
applyReducedAdjugateProduct Y operator X =
  trans
    (applyReducedComposition Y operator
      (reducedAdjointAdjugate Y operator) X)
    (trans
      (cong
        (λ composed → applyReducedAdjoint Y composed X)
        (reducedAdjointAdjugateProduct Y operator))
      (applyScaleIdentityReduced Y
        (reducedAdjointDeterminantValue Y operator) X))
