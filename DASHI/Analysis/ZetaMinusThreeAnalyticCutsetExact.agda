module DASHI.Analysis.ZetaMinusThreeAnalyticCutsetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ZetaMinusThreeBernoulliArithmeticExact as Arithmetic

------------------------------------------------------------------------
-- ZETA(-3) ANALYTIC CUTSET
--
-- The rational arithmetic is already owned in the adjacent arithmetic owner.
-- What remains is the actual analytic continuation / Bernoulli special-value
-- theorem and a same-object identification of the continued function.
------------------------------------------------------------------------

record RiemannZetaContinuationCarrier : Set₁ where
  field
    Complex : Set
    Rational : Set
    zeta : Complex → Complex
    embedRational : Rational → Complex
    minusThree : Complex
    oneOverOneTwenty : Rational
    reading : String

open RiemannZetaContinuationCarrier public

record BernoulliFourAnalyticReceipt
    (Z : RiemannZetaContinuationCarrier) : Set₁ where
  field
    Bernoulli : Set
    B4 : Bernoulli

    analyticContinuationExistsAtMinusThree : Set
    bernoulliSpecialValueTheorem : Set
    b4EqualsMinusOneOverThirty : Set
    zetaMinusThreeEqualsMinusB4OverFour : Set
    sameContinuedZetaObject : Set
    reading : String

open BernoulliFourAnalyticReceipt public

record ZetaMinusThreeOneOver120Receipt
    (Z : RiemannZetaContinuationCarrier) : Set₁ where
  field
    analytic : BernoulliFourAnalyticReceipt Z
    rationalCompiler : Arithmetic.ZetaMinusThreeArithmeticReceipt
    rationalCompilerUsesB4 : Set
    zetaMinusThreeEqualsOneOver120 : Set
    reading : String

open ZetaMinusThreeOneOver120Receipt public

data BernoulliArithmeticAutomaticallySuppliesAnalyticContinuation : Set where

data AnalyticContinuationAutomaticallyIdentifiesCasimirDefect : Set where

arithmeticDoesNotSupplyContinuation :
  BernoulliArithmeticAutomaticallySuppliesAnalyticContinuation → ⊥
arithmeticDoesNotSupplyContinuation ()

continuationDoesNotSupplyApplicationIdentity :
  AnalyticContinuationAutomaticallyIdentifiesCasimirDefect → ⊥
continuationDoesNotSupplyApplicationIdentity ()
