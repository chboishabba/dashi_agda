module DASHI.Physics.YangMills.BalabanSU2AdjointRotationDeterminant where

------------------------------------------------------------------------
-- Matrix and determinant of the SU(2) adjoint action.
--
-- Quaternion conjugation acts on the imaginary coordinates by the familiar
-- 3 x 3 rotation matrix.  For a general quaternion its determinant is the
-- cube of the quaternion norm squared; for a unit quaternion it is exactly
-- one.  This makes the background gauge-basis determinant cancellation
-- literal rather than an abstract assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
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
  ; oneR
  ; *-identityˡ
  ; normSquaredQ
  ; normSquaredExpand
  ; realSolverRing
  ; SU2Quaternion
  ; su2q
  ; quaternion
  ; unitNormSquared
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; su2Adjoint
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointMatrixDeterminant using
  ( Matrix3
  ; matrix3
  ; applyMatrix3
  ; determinantMatrix3
  )

twoR : ℝ
twoR = oneR +R oneR

su2AdjointMatrix : SU2Quaternion → Matrix3
su2AdjointMatrix (su2q (quat a b c d) unit) =
  matrix3
    ((((a *R a) +R (b *R b)) +R (-R (c *R c))) +R (-R (d *R d)))
    (twoR *R ((b *R c) +R (-R (a *R d))))
    (twoR *R ((b *R d) +R (a *R c)))

    (twoR *R ((b *R c) +R (a *R d)))
    ((((a *R a) +R (-R (b *R b))) +R (c *R c)) +R (-R (d *R d)))
    (twoR *R ((c *R d) +R (-R (a *R b))))

    (twoR *R ((b *R d) +R (-R (a *R c))))
    (twoR *R ((c *R d) +R (a *R b)))
    ((((a *R a) +R (-R (b *R b))) +R (-R (c *R c))) +R (d *R d))

applySU2AdjointMatrix :
  ∀ u X →
  applyMatrix3 (su2AdjointMatrix u) X ≡ su2Adjoint u X
applySU2AdjointMatrix
  (su2q (quat a b c d) unit)
  (su2Lie x y z) =
  su2LieExt
    (Solver.solve
      (a ∷ b ∷ c ∷ d ∷ x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ d ∷ x ∷ y ∷ z ∷ []) realSolverRing)
    (Solver.solve
      (a ∷ b ∷ c ∷ d ∷ x ∷ y ∷ z ∷ []) realSolverRing)

su2AdjointMatrixDeterminantNormCube :
  ∀ u →
  determinantMatrix3 (su2AdjointMatrix u)
    ≡
  normSquaredQ (quaternion u)
    *R (normSquaredQ (quaternion u)
      *R normSquaredQ (quaternion u))
su2AdjointMatrixDeterminantNormCube
  (su2q q@(quat a b c d) unit)
  rewrite normSquaredExpand q =
  Solver.solve (a ∷ b ∷ c ∷ d ∷ []) realSolverRing

su2AdjointMatrixDeterminantOne :
  ∀ u →
  determinantMatrix3 (su2AdjointMatrix u) ≡ oneR
su2AdjointMatrixDeterminantOne u =
  trans
    (su2AdjointMatrixDeterminantNormCube u)
    (trans
      (cong
        (λ norm → norm *R (norm *R norm))
        (unitNormSquared u))
      (trans
        (*-identityˡ (oneR *R oneR))
        (*-identityˡ oneR)))
