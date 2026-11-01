module DASHI.Analysis.ZetaMinusThreeFiniteAnalyticBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.BernoulliFourCubicFiniteDifferenceExact as Finite
import DASHI.Analysis.ZetaMinusThreeBernoulliArithmeticExact as Arithmetic
import DASHI.Analysis.ZetaMinusThreeSourceAuthorityExact as Source
import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport

------------------------------------------------------------------------
-- zeta(-3): FINITE / ANALYTIC BIDI SPLIT
--
-- OWNED finite algebra:
--   B4(x+1) - B4(x) = 4 x^3
--   B4 = -1/30  ->  -B4/4 = 1/120  (adjacent arithmetic owner)
--
-- NOT owned by the finite algebra:
--   analytic continuation identifying zeta(-3) with -B4/4.
--
-- This makes the reverse proof search precise: once a consumer asks for the
-- longitudinal cubic finite part, the finite-difference owner explains why B4
-- is the right Bernoulli object; the remaining producer is the analytic
-- continuation/same-object weld, not another coefficient calculation.
------------------------------------------------------------------------

record CubicBernoulliFiniteOwner : Set₁ where
  field
    finiteDifferenceFamily : Set
    finiteDifferenceReceipt : Set
    cubicCoefficientFourOwned : Set
    bernoulliFourPolynomialOwned : Set
    reading : String

open CubicBernoulliFiniteOwner public

canonicalCubicBernoulliFiniteOwner : CubicBernoulliFiniteOwner
canonicalCubicBernoulliFiniteOwner = record
  { finiteDifferenceFamily = ⊤
  ; finiteDifferenceReceipt = ⊤
  ; cubicCoefficientFourOwned = ⊤
  ; bernoulliFourPolynomialOwned = ⊤
  ; reading = "The rational ring solver owns B4(x+1)-B4(x)=4x^3; no analytic continuation is used."
  }

record AnalyticContinuationWeld : Set₁ where
  field
    sourceAuthority : Source.ZetaMinusThreeSourceAuthority
    sameZetaObject : Set
    sameBernoulliConvention : Set
    sameNormalisationAtMinusThree : Set
    continuationValidAtMinusThree : Set
    localZetaMinusThreeEqualsMinusB4OverFour : Set
    reading : String

open AnalyticContinuationWeld public

record ReverseCubicFinitePartObligations : Set where
  field
    transformedCasimirDefectIsCubic : Set
    finiteDifferenceMatchesBernoulliFour : Set
    continuationWeld : Set
    bernoulliValueB4MinusOneThirtieth : Set
    sameCoefficientNormalisation : Set

open ReverseCubicFinitePartObligations public

data FiniteBernoulliIdentityAutomaticallyGivesAnalyticContinuation : Set where

data SourceSpecialValueAutomaticallyIdentifiesCasimirDefect : Set where

finiteDoesNotAutoContinue :
  FiniteBernoulliIdentityAutomaticallyGivesAnalyticContinuation → ⊥
finiteDoesNotAutoContinue ()

sourceValueDoesNotAutoWeldCasimir :
  SourceSpecialValueAutomaticallyIdentifiesCasimirDefect → ⊥
sourceValueDoesNotAutoWeldCasimir ()

record Status : Set where
  field
    b4CubicFiniteDifferenceOwned : Bool
    b4ToOneOver120ArithmeticOwned : Bool
    zetaMinusThreeSourceBacked : Bool
    internalAnalyticContinuationClosed : Bool
    casimirDefectSameObjectWeldClosed : Bool

    b4CubicFiniteDifferenceOwnedIsTrue : b4CubicFiniteDifferenceOwned ≡ true
    b4ToOneOver120ArithmeticOwnedIsTrue : b4ToOneOver120ArithmeticOwned ≡ true
    zetaMinusThreeSourceBackedIsTrue : zetaMinusThreeSourceBacked ≡ true
    internalAnalyticContinuationClosedIsFalse : internalAnalyticContinuationClosed ≡ false
    casimirDefectSameObjectWeldClosedIsFalse : casimirDefectSameObjectWeldClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { b4CubicFiniteDifferenceOwned = true
  ; b4ToOneOver120ArithmeticOwned = true
  ; zetaMinusThreeSourceBacked = true
  ; internalAnalyticContinuationClosed = false
  ; casimirDefectSameObjectWeldClosed = false
  ; b4CubicFiniteDifferenceOwnedIsTrue = refl
  ; b4ToOneOver120ArithmeticOwnedIsTrue = refl
  ; zetaMinusThreeSourceBackedIsTrue = refl
  ; internalAnalyticContinuationClosedIsFalse = refl
  ; casimirDefectSameObjectWeldClosedIsFalse = refl
  }
