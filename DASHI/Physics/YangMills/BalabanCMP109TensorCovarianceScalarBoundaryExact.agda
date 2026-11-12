module DASHI.Physics.YangMills.BalabanCMP109TensorCovarianceScalarBoundaryExact where

-- PRIMARY SOURCE: T. Balaban, CMP 109 (1987), pages 292-297,
-- equations (5.6), (5.7), (5.39)--(5.42).
-- The source grants tensor covariance; an OFF-DIAGONAL tensor component
-- is not invariant under one-coordinate reflection without a
-- compensating transformed index/sign. This module formalizes exactly
-- that source-indexed obstruction, using the original AxisIndex carrier.
--
-- It must NOT be mistaken for an actual Wilson/ghost/Haar scalar
-- source identification or for four certified physical quadratures.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (_≢_)
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval

data OrientationSign : Set where
  positive negative : OrientationSign

infixl 7 _sign*_
_sign*_ : OrientationSign → OrientationSign → OrientationSign
positive sign* other = other
negative sign* positive = negative
negative sign* negative = positive

flip0IndexSign : Eval.AxisIndex → OrientationSign
flip0IndexSign Eval.axis0 = negative
flip0IndexSign Eval.axis1 = positive
flip0IndexSign Eval.axis2 = positive
flip0IndexSign Eval.axis3 = positive

flip0TensorComponentSign :
  Eval.AxisIndex → Eval.AxisIndex → OrientationSign
flip0TensorComponentSign μ ν =
  flip0IndexSign μ sign* flip0IndexSign ν

-- The elementary exact sign cases from source equation (5.7).
flip0Tensor00Positive :
  flip0TensorComponentSign Eval.axis0 Eval.axis0 ≡ positive
flip0Tensor00Positive = refl

flip0Tensor11Positive :
  flip0TensorComponentSign Eval.axis1 Eval.axis1 ≡ positive
flip0Tensor11Positive = refl

flip0Tensor01Negative :
  flip0TensorComponentSign Eval.axis0 Eval.axis1 ≡ negative
flip0Tensor01Negative = refl

flip0Tensor10Negative :
  flip0TensorComponentSign Eval.axis1 Eval.axis0 ≡ negative
flip0Tensor10Negative = refl

-- Therefore the off-diagonal tensor transformation is NOT itself an
-- unrestricted equality of every component. A scalar needs a genuine
-- invariant contraction/projection before invoking the four-orbit theorem.
offDiagonalFlipIsNotUnsigned :
  flip0TensorComponentSign Eval.axis0 Eval.axis1 ≢ positive
offDiagonalFlipIsNotUnsigned ()

-- Source eq. (5.42): beta is extracted from the mixed momentum
-- derivative of Pi_12 at zero (or its moment). That extraction needs
-- derivative/limit transport; it is not a declaration that Pi_12(p)
-- is invariant as an arbitrary function of p.
