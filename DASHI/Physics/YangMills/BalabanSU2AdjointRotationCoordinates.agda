module DASHI.Physics.YangMills.BalabanSU2AdjointRotationCoordinates where

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)
import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( quat; q1; q2; q3; _+R_; _*R_; -R_; zeroR; oneR; realSolverRing
  ; q1Multiply; q2Multiply; q3Multiply
  ; q0Conjugate; q1Conjugate; q2Conjugate; q3Conjugate
  ; conjugateQ; _*q_ )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( su2Lie; lieQuaternion
  ; adjointInner0; adjointInner1; adjointInner2; adjointInner3 )

twoR : ℝ
twoR = oneR +R oneR

row00 row01 row02 row10 row11 row12 row20 row21 row22 :
  ℝ → ℝ → ℝ → ℝ → ℝ
row00 a b c d = (((a *R a) +R (b *R b)) +R (-R (c *R c))) +R (-R (d *R d))
row01 a b c d = twoR *R ((b *R c) +R (-R (a *R d)))
row02 a b c d = twoR *R ((b *R d) +R (a *R c))
row10 a b c d = twoR *R ((b *R c) +R (a *R d))
row11 a b c d = (((a *R a) +R (-R (b *R b))) +R (c *R c)) +R (-R (d *R d))
row12 a b c d = twoR *R ((c *R d) +R (-R (a *R b)))
row20 a b c d = twoR *R ((b *R d) +R (-R (a *R c)))
row21 a b c d = twoR *R ((c *R d) +R (a *R b))
row22 a b c d = (((a *R a) +R (-R (b *R b))) +R (-R (c *R c))) +R (d *R d)

rotationX rotationY rotationZ :
  ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
rotationX a b c d x y z =
  ((row00 a b c d *R x) +R (row01 a b c d *R y)) +R (row02 a b c d *R z)
rotationY a b c d x y z =
  ((row10 a b c d *R x) +R (row11 a b c d *R y)) +R (row12 a b c d *R z)
rotationZ a b c d x y z =
  ((row20 a b c d *R x) +R (row21 a b c d *R y)) +R (row22 a b c d *R z)

adjointXCoordinate : ∀ a b c d x y z →
  rotationX a b c d x y z ≡
  q1 ((quat a b c d *q lieQuaternion (su2Lie x y z)) *q conjugateQ (quat a b c d))
adjointXCoordinate a b c d x y z
  rewrite q1Multiply (quat a b c d *q lieQuaternion (su2Lie x y z)) (conjugateQ (quat a b c d))
    | adjointInner0 a b c d x y z
    | adjointInner1 a b c d x y z
    | adjointInner2 a b c d x y z
    | adjointInner3 a b c d x y z
    | q0Conjugate (quat a b c d)
    | q1Conjugate (quat a b c d)
    | q2Conjugate (quat a b c d)
    | q3Conjugate (quat a b c d) =
  Solver.solve (a ∷ b ∷ c ∷ d ∷ x ∷ y ∷ z ∷ []) realSolverRing

adjointYCoordinate : ∀ a b c d x y z →
  rotationY a b c d x y z ≡
  q2 ((quat a b c d *q lieQuaternion (su2Lie x y z)) *q conjugateQ (quat a b c d))
adjointYCoordinate a b c d x y z
  rewrite q2Multiply (quat a b c d *q lieQuaternion (su2Lie x y z)) (conjugateQ (quat a b c d))
    | adjointInner0 a b c d x y z
    | adjointInner1 a b c d x y z
    | adjointInner2 a b c d x y z
    | adjointInner3 a b c d x y z
    | q0Conjugate (quat a b c d)
    | q1Conjugate (quat a b c d)
    | q2Conjugate (quat a b c d)
    | q3Conjugate (quat a b c d) =
  Solver.solve (a ∷ b ∷ c ∷ d ∷ x ∷ y ∷ z ∷ []) realSolverRing

adjointZCoordinate : ∀ a b c d x y z →
  rotationZ a b c d x y z ≡
  q3 ((quat a b c d *q lieQuaternion (su2Lie x y z)) *q conjugateQ (quat a b c d))
adjointZCoordinate a b c d x y z
  rewrite q3Multiply (quat a b c d *q lieQuaternion (su2Lie x y z)) (conjugateQ (quat a b c d))
    | adjointInner0 a b c d x y z
    | adjointInner1 a b c d x y z
    | adjointInner2 a b c d x y z
    | adjointInner3 a b c d x y z
    | q0Conjugate (quat a b c d)
    | q1Conjugate (quat a b c d)
    | q2Conjugate (quat a b c d)
    | q3Conjugate (quat a b c d) =
  Solver.solve (a ∷ b ∷ c ∷ d ∷ x ∷ y ∷ z ∷ []) realSolverRing
