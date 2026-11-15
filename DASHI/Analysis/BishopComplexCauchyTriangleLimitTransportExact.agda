module DASHI.Analysis.BishopComplexCauchyTriangleLimitTransportExact where

------------------------------------------------------------------------
-- BISHOP COMPLEX SQUARE -> CAUCHY TRIANGLE LIMIT TRANSPORT.
--
-- No generic complex convergence postulate:
-- apply the existing scalar Bishop vanishing-difference theorem to
-- each Cartesian coordinate. The exact difference is the original
-- Wing.upperWingResidual = rectangle - triangle.
--
-- The second theorem specializes this transport to the ACTUAL
-- factorial series streams and their now source-written four
-- vanishing-wing certificates.
--
-- Remaining after this transport: original square rectangle limits,
-- actual complex binomial coefficient sum = factorial (z+w) term,
-- and pinned Agda 2.9 kernel checking.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexFiniteRectangleProductExact as Rectangle
import DASHI.Analysis.BishopComplexFiniteSquareTriangleDifferenceExact as Wing
import DASHI.Analysis.BishopComplexTriangleTailsVanishingExact as Factorial
import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as Vanish

originalBishopComplexTriangleRealDifferenceBound :
  ∀ (left right : Nat → Complex.BishopComplex) n →
  BishopReal._≤_
    (BishopReal.∣ BishopReal._-_
      (Complex.re (Wing.cauchyTrianglePartial left right n))
      (Complex.re (Rectangle.rectangleComplex left right n n)) ∣)
    (BishopReal.∣
      (Complex.re (Wing.upperWingResidual left right n)) ∣)
originalBishopComplexTriangleRealDifferenceBound left right n =
  let
    r = Complex.re (Rectangle.rectangleComplex left right n n)
    t = Complex.re (Wing.cauchyTrianglePartial left right n)
    symmetricDifference :
      BishopReal._≃_
        (BishopReal._-_ t r)
        (BishopReal.-_ (BishopReal._-_ r t))
    symmetricDifference =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ r′ t′ → t′ ⊖ r′ ⊜ ⊝ (r′ ⊖ t′))
        BishopP.≃-refl r t
  in
  BishopP.≤-reflexive
    (BishopP.≃-trans
      (BishopP.∣-∣-cong symmetricDifference)
      BishopP.∣-x∣≃∣x∣)

originalBishopComplexTriangleImagDifferenceBound :
  ∀ (left right : Nat → Complex.BishopComplex) n →
  BishopReal._≤_
    (BishopReal.∣ BishopReal._-_
      (Complex.im (Wing.cauchyTrianglePartial left right n))
      (Complex.im (Rectangle.rectangleComplex left right n n)) ∣)
    (BishopReal.∣
      (Complex.im (Wing.upperWingResidual left right n)) ∣)
originalBishopComplexTriangleImagDifferenceBound left right n =
  let
    r = Complex.im (Rectangle.rectangleComplex left right n n)
    t = Complex.im (Wing.cauchyTrianglePartial left right n)
    symmetricDifference :
      BishopReal._≃_
        (BishopReal._-_ t r)
        (BishopReal.-_ (BishopReal._-_ r t))
    symmetricDifference =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ r′ t′ → t′ ⊖ r′ ⊜ ⊝ (r′ ⊖ t′))
        BishopP.≃-refl r t
  in
  BishopP.≤-reflexive
    (BishopP.≃-trans
      (BishopP.∣-∣-cong symmetricDifference)
      BishopP.∣-x∣≃∣x∣)

originalBishopComplexTriangleLimitTransport :
  (left right : Nat → Complex.BishopComplex) →
  (target : Complex.BishopComplex) →
  BishopSequence._ConvergesTo_
    (λ n → Complex.re (Rectangle.rectangleComplex left right n n))
    (Complex.re target) →
  BishopSequence._ConvergesTo_
    (λ n → Complex.im (Rectangle.rectangleComplex left right n n))
    (Complex.im target) →
  BishopSequence._ConvergesTo_
    (λ n → Complex.re (Wing.upperWingResidual left right n))
    BishopReal.0ℝ →
  BishopSequence._ConvergesTo_
    (λ n → Complex.im (Wing.upperWingResidual left right n))
    BishopReal.0ℝ →
  BishopSequence._ConvergesTo_
    (λ n → Complex.re (Wing.cauchyTrianglePartial left right n))
    (Complex.re target)
  ×
  BishopSequence._ConvergesTo_
    (λ n → Complex.im (Wing.cauchyTrianglePartial left right n))
    (Complex.im target)
originalBishopComplexTriangleLimitTransport
  left right target rectangleReal rectangleImag wingReal wingImag =
  (Vanish.vanishingDifferenceConvergence
    rectangleReal wingReal
    (originalBishopComplexTriangleRealDifferenceBound left right))
  ,
  (Vanish.vanishingDifferenceConvergence
    rectangleImag wingImag
    (originalBishopComplexTriangleImagDifferenceBound left right))

-- Specialization: actual factorial coefficients on the genuine
-- real and imaginary axes; no hypothetical wing convergence.
originalBishopFactorialTriangleFromRectangle :
  ∀ x y (target : Complex.BishopComplex) →
  BishopSequence._ConvergesTo_
    (λ n → Complex.re
      (Rectangle.rectangleComplex
        (Factorial.factorialRealStream x)
        (Factorial.factorialImaginaryStream y)
        n n))
    (Complex.re target) →
  BishopSequence._ConvergesTo_
    (λ n → Complex.im
      (Rectangle.rectangleComplex
        (Factorial.factorialRealStream x)
        (Factorial.factorialImaginaryStream y)
        n n))
    (Complex.im target) →
  BishopSequence._ConvergesTo_
    (λ n → Complex.re
      (Wing.cauchyTrianglePartial
        (Factorial.factorialRealStream x)
        (Factorial.factorialImaginaryStream y) n))
    (Complex.re target)
  ×
  BishopSequence._ConvergesTo_
    (λ n → Complex.im
      (Wing.cauchyTrianglePartial
        (Factorial.factorialRealStream x)
        (Factorial.factorialImaginaryStream y) n))
    (Complex.im target)
originalBishopFactorialTriangleFromRectangle
  x y target rectangleReal rectangleImag =
  originalBishopComplexTriangleLimitTransport
    (Factorial.factorialRealStream x)
    (Factorial.factorialImaginaryStream y)
    target
    rectangleReal rectangleImag
    (Factorial.originalBishopFactorialComplexWingRealConvergesZero x y)
    (Factorial.originalBishopFactorialComplexWingImagConvergesZero x y)
