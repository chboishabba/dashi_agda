module DASHI.Analysis.ZetaMinusThreeAnalyticCutsetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Rational using (ℚ)

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
    zeta : Complex → Complex
    embedRational : ℚ → Complex
    minusThree : Complex
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
    rationalCompiler :
      Arithmetic.minusB4OverFour ≡ Arithmetic.oneOver120
    rationalCompilerUsesB4 : Set
    zetaMinusThreeEqualsOneOver120 :
      zeta Z (minusThree Z) ≡ embedRational Z Arithmetic.oneOver120
    reading : String

open ZetaMinusThreeOneOver120Receipt public

canonicalBernoulliArithmetic :
  Arithmetic.minusB4OverFour ≡ Arithmetic.oneOver120
canonicalBernoulliArithmetic = Arithmetic.bernoulliB4CompilerProducesOneOver120

data BernoulliArithmeticAutomaticallySuppliesAnalyticContinuation : Set where

data AnalyticContinuationAutomaticallyIdentifiesCasimirDefect : Set where

arithmeticDoesNotSupplyContinuation :
  BernoulliArithmeticAutomaticallySuppliesAnalyticContinuation → ⊥
arithmeticDoesNotSupplyContinuation ()

continuationDoesNotSupplyApplicationIdentity :
  AnalyticContinuationAutomaticallyIdentifiesCasimirDefect → ⊥
continuationDoesNotSupplyApplicationIdentity ()
