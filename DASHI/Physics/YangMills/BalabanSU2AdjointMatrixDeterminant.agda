module DASHI.Physics.YangMills.BalabanSU2AdjointMatrixDeterminant where

------------------------------------------------------------------------
-- Concrete 3 x 3 matrices for the su(2) adjoint calculus.
--
-- In the coordinate basis of pure-imaginary quaternions, ad_y is a real
-- skew-symmetric 3 x 3 matrix.  This module constructs that matrix, proves it
-- acts as the previously defined Lie bracket, and computes the exact
-- determinant of
--
--   a I + b ad_y + c ad_y^2.
--
-- Writing k = -4 <y,y>, the result is
--
--   det(a I + b A + c A^2)
--     = a ((a + c k)^2 - k b^2).
--
-- This is literal finite determinant algebra, not a positivity or asymptotic
-- estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)

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
  )
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  ( adOperator )
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  ( adCubicCoefficient )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( ReducedAdjointOperator
  ; reducedAd
  ; identityCoefficient
  ; linearCoefficient
  ; quadraticCoefficient
  ; applyReducedAdjoint
  )

record Matrix3 : Set where
  constructor matrix3
  field
    m00 m01 m02 : ℝ
    m10 m11 m12 : ℝ
    m20 m21 m22 : ℝ

open Matrix3 public

matrix3Ext :
  ∀ {A B : Matrix3} →
  m00 A ≡ m00 B → m01 A ≡ m01 B → m02 A ≡ m02 B →
  m10 A ≡ m10 B → m11 A ≡ m11 B → m12 A ≡ m12 B →
  m20 A ≡ m20 B → m21 A ≡ m21 B → m22 A ≡ m22 B →
  A ≡ B
matrix3Ext
  {matrix3 a00 a01 a02 a10 a11 a12 a20 a21 a22}
  {matrix3 .a00 .a01 .a02 .a10 .a11 .a12 .a20 .a21 .a22}
  refl refl refl refl refl refl refl refl refl = refl

identityMatrix3 : Matrix3
identityMatrix3 =
  matrix3
    oneR zeroR zeroR
    zeroR oneR zeroR
    zeroR zeroR oneR

addMatrix3 : Matrix3 → Matrix3 → Matrix3
addMatrix3
  (matrix3 a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (matrix3 b00 b01 b02 b10 b11 b12 b20 b21 b22) =
  matrix3
    (a00 +R b00) (a01 +R b01) (a02 +R b02)
    (a10 +R b10) (a11 +R b11) (a12 +R b12)
    (a20 +R b20) (a21 +R b21) (a22 +R b22)

scaleMatrix3 : ℝ → Matrix3 → Matrix3
scaleMatrix3 scalar
  (matrix3 a00 a01 a02 a10 a11 a12 a20 a21 a22) =
  matrix3
    (scalar *R a00) (scalar *R a01) (scalar *R a02)
    (scalar *R a10) (scalar *R a11) (scalar *R a12)
    (scalar *R a20) (scalar *R a21) (scalar *R a22)

multiplyMatrix3 : Matrix3 → Matrix3 → Matrix3
multiplyMatrix3
  (matrix3 a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (matrix3 b00 b01 b02 b10 b11 b12 b20 b21 b22) =
  matrix3
    (((a00 *R b00) +R (a01 *R b10)) +R (a02 *R b20))
    (((a00 *R b01) +R (a01 *R b11)) +R (a02 *R b21))
    (((a00 *R b02) +R (a01 *R b12)) +R (a02 *R b22))
    (((a10 *R b00) +R (a11 *R b10)) +R (a12 *R b20))
    (((a10 *R b01) +R (a11 *R b11)) +R (a12 *R b21))
    (((a10 *R b02) +R (a11 *R b12)) +R (a12 *R b22))
    (((a20 *R b00) +R (a21 *R b10)) +R (a22 *R b20))
    (((a20 *R b01) +R (a21 *R b11)) +R (a22 *R b21))
    (((a20 *R b02) +R (a21 *R b12)) +R (a22 *R b22))

applyMatrix3 : Matrix3 → SU2LieAlgebra → SU2LieAlgebra
applyMatrix3
  (matrix3 a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (su2Lie x y z) =
  su2Lie
    (((a00 *R x) +R (a01 *R y)) +R (a02 *R z))
    (((a10 *R x) +R (a11 *R y)) +R (a12 *R z))
    (((a20 *R x) +R (a21 *R y)) +R (a22 *R z))

determinantMatrix3 : Matrix3 → ℝ
determinantMatrix3
  (matrix3 a b c d e f g h i) =
  (a *R ((e *R i) +R (-R (f *R h))))
  +R (-R (b *R ((d *R i) +R (-R (f *R g)))))
  +R (c *R ((d *R h) +R (-R (e *R g))))

twoR : ℝ
twoR = oneR +R oneR

adMatrix : SU2LieAlgebra → Matrix3
adMatrix (su2Lie x y z) =
  matrix3
    zeroR        (-R (twoR *R z)) (twoR *R y)
    (twoR *R z) zeroR             (-R (twoR *R x))
    (-R (twoR *R y)) (twoR *R x) zeroR

applyAdMatrix :
  ∀ Y X → applyMatrix3 (adMatrix Y) X ≡ adOperator Y X
applyAdMatrix
  (su2Lie y₁ y₂ y₃)
  (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (Solver.solve (y₁ ∷ y₂ ∷ y₃ ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) realSolverRing)
    (Solver.solve (y₁ ∷ y₂ ∷ y₃ ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) realSolverRing)
    (Solver.solve (y₁ ∷ y₂ ∷ y₃ ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) realSolverRing)

reducedAdjointMatrix :
  SU2LieAlgebra → ReducedAdjointOperator → Matrix3
reducedAdjointMatrix Y operator =
  addMatrix3
    (scaleMatrix3 (identityCoefficient operator) identityMatrix3)
    (addMatrix3
      (scaleMatrix3 (linearCoefficient operator) (adMatrix Y))
      (scaleMatrix3 (quadraticCoefficient operator)
        (multiplyMatrix3 (adMatrix Y) (adMatrix Y))))

applyReducedAdjointMatrix :
  ∀ Y operator X →
  applyMatrix3 (reducedAdjointMatrix Y operator) X
    ≡ applyReducedAdjoint Y operator X
applyReducedAdjointMatrix
  (su2Lie y₁ y₂ y₃)
  (reducedAd a b c)
  (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (Solver.solve
      (y₁ ∷ y₂ ∷ y₃ ∷ a ∷ b ∷ c ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (y₁ ∷ y₂ ∷ y₃ ∷ a ∷ b ∷ c ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)
    (Solver.solve
      (y₁ ∷ y₂ ∷ y₃ ∷ a ∷ b ∷ c ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])
      realSolverRing)

reducedAdjointDeterminant :
  ∀ Y a b c →
  determinantMatrix3
    (reducedAdjointMatrix Y (reducedAd a b c))
  ≡
  a *R
    (((a +R (c *R adCubicCoefficient Y))
       *R (a +R (c *R adCubicCoefficient Y)))
      +R (-R (adCubicCoefficient Y *R (b *R b))))
reducedAdjointDeterminant
  (su2Lie y₁ y₂ y₃) a b c =
  Solver.solve
    (y₁ ∷ y₂ ∷ y₃ ∷ a ∷ b ∷ c ∷ [])
    realSolverRing
