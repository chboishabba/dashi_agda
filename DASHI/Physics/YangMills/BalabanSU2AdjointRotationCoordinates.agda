module DASHI.Physics.YangMills.BalabanSU2AdjointRotationCoordinates where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (quat; q1; q2; q3; q1Multiply; q2Multiply; q3Multiply
  ; q0Conjugate; q1Conjugate; q2Conjugate; q3Conjugate
  ; conjugateQ; _*q_)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (su2Lie; lieQuaternion
  ; adjointInner0; adjointInner1; adjointInner2; adjointInner3)
open import DASHI.Physics.YangMills.BalabanSU2AdjointRotationScalar public using
  (row00; row01; row02; row10; row11; row12; row20; row21; row22
  ; rotationX; rotationY; rotationZ)
open import DASHI.Physics.YangMills.BalabanSU2AdjointRotationPolynomial using
  (adjointXPolynomial; adjointYPolynomial; adjointZPolynomial)

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
  adjointXPolynomial a b c d x y z

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
  adjointYPolynomial a b c d x y z

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
  adjointZPolynomial a b c d x y z
