module DASHI.Analysis.RiemannG21ActualTaperOddMomentSupportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SupportMomentDominationExact as Generic
import DASHI.Analysis.RiemannG21OddTaylorSourceBudgetBoundary as Source

------------------------------------------------------------------------
-- Actual-taper specialization of compact-support moment domination.
--
-- For height y>0 and support radius R=L/2 define schematically
--
--   N1(y) = integral_0^R u   phi(u) sinh(yu) du
--   N3(y) = integral_0^R u^3 phi(u) sinh(yu) du
--   N5(y) = integral_0^R u^5 phi(u) sinh(yu) du.
--
-- Because the common weight u phi(u) sinh(yu) is nonnegative and 0<=u<=R,
-- the pointwise inequalities u^2<=R^2 and u^4<=R^4 should give
--
--   N3(y) <= R^2 N1(y),
--   N5(y) <= R^4 N1(y).
--
-- The companion source already owns 0<=phi<=1 and support in [-L/2,L/2].
-- This module makes the remaining ordered-integral monotonicity theorem an
-- explicit specialization target rather than hiding it in the Taylor budget.
------------------------------------------------------------------------

record ActualOddMomentFamily : Set₁ where
  field
    Height Radius Scalar : Set
    height : Height
    supportRadius : Radius

    n1 n3 n5 : Height → Scalar
    radiusSquare radiusFourth : Radius → Scalar
    multiply : Scalar → Scalar → Scalar

    Nonnegative : Scalar → Set
    LessOrEqual : Scalar → Scalar → Set

    n1Nonnegative : Nonnegative (n1 height)
    n3Nonnegative : Nonnegative (n3 height)
    n5Nonnegative : Nonnegative (n5 height)

    n3SupportDomination :
      LessOrEqual
        (n3 height)
        (multiply (radiusSquare supportRadius) (n1 height))

    n5SupportDomination :
      LessOrEqual
        (n5 height)
        (multiply (radiusFourth supportRadius) (n1 height))

    reading : String

open ActualOddMomentFamily public

record ActualTaperOddMomentProducer : Set₁ where
  field
    Height Radius Scalar : Set
    offLineHeight poleHeight : Height
    supportRadius : Radius

    n1 n3 n5 : Height → Scalar
    radiusSquare radiusFourth : Radius → Scalar
    multiply : Scalar → Scalar → Scalar
    Nonnegative : Scalar → Set
    StrictPositive : Scalar → Set
    LessOrEqual : Scalar → Scalar → Set

    offLineN1Positive : StrictPositive (n1 offLineHeight)
    poleN1Positive : StrictPositive (n1 poleHeight)

    offLineN3Bound :
      LessOrEqual
        (n3 offLineHeight)
        (multiply (radiusSquare supportRadius) (n1 offLineHeight))
    poleN3Bound :
      LessOrEqual
        (n3 poleHeight)
        (multiply (radiusSquare supportRadius) (n1 poleHeight))

    offLineN5Bound :
      LessOrEqual
        (n5 offLineHeight)
        (multiply (radiusFourth supportRadius) (n1 offLineHeight))
    poleN5Bound :
      LessOrEqual
        (n5 poleHeight)
        (multiply (radiusFourth supportRadius) (n1 poleHeight))

    supportRadiusIsLOverTwo : Set
    producerReading : String

------------------------------------------------------------------------
-- Source receipts reused directly from the companion taper audit.
------------------------------------------------------------------------

sourceReceipt : Source.TaperSupportSourceReceipt
sourceReceipt = Source.canonicalTaperSupportSourceReceipt

genericSupportBoundary : Generic.SupportMomentDominationBoundary
genericSupportBoundary = Generic.canonicalSupportMomentDominationBoundary

record ActualTaperOddMomentBoundary : Set where
  constructor actualTaperOddMomentBoundary
  field
    actualOddMomentSpecializationConstructed : Bool
    actualOddMomentSpecializationConstructedIsTrue :
      actualOddMomentSpecializationConstructed ≡ true
    companionSupportFactsAvailable : Bool
    companionSupportFactsAvailableIsTrue :
      companionSupportFactsAvailable ≡ true
    positiveOddWeightProducerDerived : Bool
    positiveOddWeightProducerDerivedIsFalse :
      positiveOddWeightProducerDerived ≡ false
    actualN3SupportDominationDerived : Bool
    actualN3SupportDominationDerivedIsFalse :
      actualN3SupportDominationDerived ≡ false
    actualN5SupportDominationDerived : Bool
    actualN5SupportDominationDerivedIsFalse :
      actualN5SupportDominationDerived ≡ false
    actualN1StrictPositivityDerived : Bool
    actualN1StrictPositivityDerivedIsFalse :
      actualN1StrictPositivityDerived ≡ false

canonicalActualTaperOddMomentBoundary : ActualTaperOddMomentBoundary
canonicalActualTaperOddMomentBoundary =
  actualTaperOddMomentBoundary
    true refl true refl false refl false refl false refl false refl
