{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCouplingCapToInverseThresholdExact where

open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; Positive; NonNegative; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CONVERSE OF THE EXISTING INVERSE-SQUARE ORDER BRIDGE
--
-- Existing repository theorem:
--
--   u_* <= u  ->  g <= gamma
--
-- under
--
--   u g^2 = 1,    u_* gamma^2 = 1.
--
-- The converse is equally constructive over positive rationals:
--
--   g <= gamma  ->  u_* <= u.
--
-- Scale by the positive common product gamma^2 g^2.  The two exact
-- representation laws identify the scaled endpoints with g^2 and gamma^2,
-- respectively, and positive multiplication can then be cancelled.
------------------------------------------------------------------------

squareMonotonePositive :
  ∀ left right →
  Positive left →
  Positive right →
  left ≤ right →
  Order.square left ≤ Order.square right
squareMonotonePositive left right leftPositive rightPositive leftBelow =
  let
    leftNN : 0ℚ ≤ left
    leftNN = Order.positiveImpliesNonnegative left leftPositive

    rightNN : 0ℚ ≤ right
    rightNN = Order.positiveImpliesNonnegative right rightPositive

    first : left * left ≤ left * right
    first =
      let
        instance leftNonnegative : NonNegative left
        leftNonnegative = ℚ.nonNegative leftNN
      in
      ℚP.*-monoˡ-≤-nonNeg left leftBelow

    secondRaw : right * left ≤ right * right
    secondRaw =
      let
        instance rightNonnegative : NonNegative right
        rightNonnegative = ℚ.nonNegative rightNN
      in
      ℚP.*-monoˡ-≤-nonNeg right leftBelow

    second : left * right ≤ right * right
    second =
      subst
        (λ lower → lower ≤ right * right)
        (ℚP.*-comm right left)
        secondRaw
  in
  ℚP.≤-trans first second

productOfSquaresPositive :
  ∀ dataSet →
  Positive (Order.productOfSquares dataSet)
productOfSquaresPositive dataSet =
  let
    g = Order.coupling dataSet
    gamma = Order.thresholdCoupling dataSet

    instance
      gPositive : Positive g
      gPositive = Order.couplingPositive dataSet

      gammaPositive : Positive gamma
      gammaPositive = Order.thresholdCouplingPositive dataSet

      gSquarePositive : Positive (Order.square g)
      gSquarePositive = ℚP.pos*pos⇒pos g g

      gammaSquarePositive : Positive (Order.square gamma)
      gammaSquarePositive = ℚP.pos*pos⇒pos gamma gamma
  in
  ℚP.pos*pos⇒pos (Order.square gamma) (Order.square g)

smallCouplingImpliesInverseThreshold :
  ∀ dataSet →
  Order.coupling dataSet ≤ Order.thresholdCoupling dataSet →
  Order.inverseThreshold dataSet ≤ Order.inverseCoupling dataSet
smallCouplingImpliesInverseThreshold dataSet couplingBelow =
  let
    g = Order.coupling dataSet
    gamma = Order.thresholdCoupling dataSet
    product = Order.productOfSquares dataSet

    squareBelow :
      Order.square g ≤ Order.square gamma
    squareBelow =
      squareMonotonePositive
        g gamma
        (Order.couplingPositive dataSet)
        (Order.thresholdCouplingPositive dataSet)
        couplingBelow

    squareBelowScaledInverse :
      Order.square g
      ≤ product * Order.inverseCoupling dataSet
    squareBelowScaledInverse =
      subst
        (λ right → Order.square g ≤ right)
        (sym (Order.scaledInverseCouplingMeaning dataSet))
        squareBelow

    scaled :
      product * Order.inverseThreshold dataSet
      ≤ product * Order.inverseCoupling dataSet
    scaled =
      subst
        (λ left → left ≤ product * Order.inverseCoupling dataSet)
        (sym (Order.scaledThresholdMeaning dataSet))
        squareBelowScaledInverse

    instance
      productPositive : Positive product
      productPositive = productOfSquaresPositive dataSet
  in
  ℚP.*-cancelˡ-≤-pos product scaled

couplingCapToInverseThresholdCompilerLevel : ProofLevel
couplingCapToInverseThresholdCompilerLevel = machineChecked
