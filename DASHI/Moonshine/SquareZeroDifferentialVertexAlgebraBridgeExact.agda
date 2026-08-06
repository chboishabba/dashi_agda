module DASHI.Moonshine.SquareZeroDifferentialVertexAlgebraBridgeExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Instantiate the generic finite differential-vertex construction with the
-- concrete square-zero algebra A=Q+Qx+Qy, D(x)=y, D(y)=0.  This confirms that
-- the generic theorem and the independently checked coordinate construction
-- agree on their vacuum, creation, translation and locality surfaces.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.FiniteDifferentialVertexAlgebraExact as Generic
import DASHI.Moonshine.SquareZeroDifferentialVertexAlgebraExact as Concrete

squareZeroDifferentialAlgebra : Generic.SquareZeroDifferentialAlgebra
squareZeroDifferentialAlgebra = record
  { Carrier = Concrete.SquareZeroRational
  ; zero = Concrete.zeroElement
  ; one = Concrete.oneElement
  ; add = Concrete.addElement
  ; multiply = Concrete.multiplyElement
  ; derivative = Concrete.derivative
  ; multiplyAssociative = Concrete.multiplyAssociative
  ; multiplyCommutative = Concrete.multiplyCommutative
  ; multiplyOneLeft = Concrete.multiplyOneLeft
  ; multiplyOneRight = Concrete.multiplyOneRight
  ; multiplyZeroLeft = Concrete.multiplyZeroLeft
  ; multiplyZeroRight = λ value →
      transitivity
        (Concrete.multiplyCommutative value Concrete.zeroElement)
        (Concrete.multiplyZeroLeft value)
  ; derivativeOneZero = Concrete.derivativeOneZero
  ; derivativeSquareZero = Concrete.derivativeSquareZero
  ; derivativeLeibniz = Concrete.derivativeLeibniz
  }
  where
    transitivity : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    transitivity refl second = second

genericSquareZeroVertexCertificate :
  Generic.FiniteDifferentialVertexCertificate squareZeroDifferentialAlgebra
genericSquareZeroVertexCertificate =
  Generic.canonicalFiniteDifferentialVertexCertificate
    squareZeroDifferentialAlgebra

genericAndConcreteMinusOneAgree : ∀ left right →
  Generic.vertexMode squareZeroDifferentialAlgebra
    left Generic.minusOne right
  ≡ Concrete.vertexMode left Concrete.minusOne right
genericAndConcreteMinusOneAgree left right = refl

genericAndConcreteMinusTwoAgree : ∀ left right →
  Generic.vertexMode squareZeroDifferentialAlgebra
    left Generic.minusTwo right
  ≡ Concrete.vertexMode left Concrete.minusTwo right
genericAndConcreteMinusTwoAgree left right = refl

genericAndConcreteFieldsAgree : ∀ value input →
  Generic.vertexField squareZeroDifferentialAlgebra value input
  ≡ Generic.truncatedField
      (Concrete.constantCoefficient (Concrete.vertexField value input))
      (Concrete.linearCoefficient (Concrete.vertexField value input))
genericAndConcreteFieldsAgree value input = refl

genericLocalityRecoversConcreteLocality : ∀ a b c →
  Generic.leftThenRightField squareZeroDifferentialAlgebra a b c
  ≡ Generic.rightThenLeftField squareZeroDifferentialAlgebra a b c
genericLocalityRecoversConcreteLocality a b c =
  Generic.truncatedVertexFieldsCommute
    squareZeroDifferentialAlgebra a b c
