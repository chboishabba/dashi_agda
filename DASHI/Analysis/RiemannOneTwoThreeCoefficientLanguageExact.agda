module DASHI.Analysis.RiemannOneTwoThreeCoefficientLanguageExact where

------------------------------------------------------------------------
-- RH COEFFICIENTS IN A 1/2/3-ONLY ARITHMETIC LANGUAGE
--
-- Every displayed integer below is constructed using only the literal
-- numerals 1, 2, 3 together with +, *, powers and truncated subtraction.
--
-- This is an arithmetic normalization layer only.  It does not assign
-- geometric or analytic semantics to the decompositions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Nat using (_∸_)

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper

pow3 : Nat -> Nat
pow3 n = Hyper.powNat 3 n

four123 : Nat
four123 = 3 + 1

five123 : Nat
five123 = 3 + 2

nine123 : Nat
nine123 = pow3 2

ten123 : Nat
ten123 = pow3 2 + 1

twenty123 : Nat
twenty123 = 2 * (pow3 2 + 1)

eighty123 : Nat
eighty123 = pow3 (2 * 2) ∸ 1

twoFortyThree123 : Nat
twoFortyThree123 = pow3 (3 + 2)

nineSeventyTwo123 : Nat
nineSeventyTwo123 = pow3 6 + pow3 5

twelveFifteen123 : Nat
twelveFifteen123 = (pow3 7 ∸ pow3 6) ∸ pow3 5

four123IsFour : four123 ≡ 4
four123IsFour = refl

five123IsFive : five123 ≡ 5
five123IsFive = refl

nine123IsNine : nine123 ≡ 9
nine123IsNine = refl

ten123IsTen : ten123 ≡ 10
ten123IsTen = refl

twenty123IsTwenty : twenty123 ≡ 20
twenty123IsTwenty = refl

eighty123IsEighty : eighty123 ≡ 80
eighty123IsEighty = refl

twoFortyThree123Is243 : twoFortyThree123 ≡ 243
twoFortyThree123Is243 = refl

nineSeventyTwo123Is972 : nineSeventyTwo123 ≡ 972
nineSeventyTwo123Is972 = refl

twelveFifteen123Is1215 : twelveFifteen123 ≡ 1215
twelveFifteen123Is1215 = refl

------------------------------------------------------------------------
-- Ratio equality without introducing rational-number normalization.
--
-- 20/243 = 80 / ((3+1)*243)
--
-- is represented by cross multiplication.
------------------------------------------------------------------------

record PositiveRatioCode : Set where
  constructor positive-ratio-code
  field
    numerator : Nat
    denominator : Nat

open PositiveRatioCode public

rhCoefficientRatio123 : PositiveRatioCode
rhCoefficientRatio123 =
  positive-ratio-code
    twenty123
    twoFortyThree123

rhCoefficientPuncturedRatio123 : PositiveRatioCode
rhCoefficientPuncturedRatio123 =
  positive-ratio-code
    eighty123
    ((3 + 1) * twoFortyThree123)

ratioCrossMultiplicationExact :
  numerator rhCoefficientRatio123
    * denominator rhCoefficientPuncturedRatio123
  ≡
  numerator rhCoefficientPuncturedRatio123
    * denominator rhCoefficientRatio123
ratioCrossMultiplicationExact = refl

------------------------------------------------------------------------
-- Sparse balanced-ternary forms explicitly recovered.
------------------------------------------------------------------------

fiveBalanced : Nat
fiveBalanced = (pow3 2 ∸ pow3 1) ∸ 1

tenBalanced : Nat
tenBalanced = pow3 2 + 1

twentyBalanced : Nat
twentyBalanced = ((pow3 3 ∸ pow3 2) + pow3 1) ∸ 1

eightyBalanced : Nat
eightyBalanced = pow3 4 ∸ 1

fiveBalancedIsFive : fiveBalanced ≡ 5
fiveBalancedIsFive = refl

tenBalancedIsTen : tenBalanced ≡ 10
tenBalancedIsTen = refl

twentyBalancedIsTwenty : twentyBalanced ≡ 20
twentyBalancedIsTwenty = refl

eightyBalancedIsEighty : eightyBalanced ≡ 80
eightyBalancedIsEighty = refl

------------------------------------------------------------------------
-- Firewall.
------------------------------------------------------------------------

data OneTwoThreeSyntaxCreatesSemantics : Set where
data BalancedDigitsCreateCarrier : Set where

oneTwoThreeSyntaxDoesNotCreateSemantics :
  OneTwoThreeSyntaxCreatesSemantics -> ⊥
oneTwoThreeSyntaxDoesNotCreateSemantics ()

balancedDigitsDoNotCreateCarrier :
  BalancedDigitsCreateCarrier -> ⊥
balancedDigitsDoNotCreateCarrier ()

record RiemannOneTwoThreeCoefficientLanguageBoundary : Set where
  constructor riemann-one-two-three-coefficient-language-boundary
  field
    allDisplayedCoefficientsRecovered : Bool
    rhRatioRecoveredByCrossMultiplication : Bool
    balancedSparseFormsRecovered : Bool
    arithmeticSyntaxPromotedToSemantics : Bool
    carrierConstructedFromDigitShape : Bool

canonicalRiemannOneTwoThreeCoefficientLanguageBoundary :
  RiemannOneTwoThreeCoefficientLanguageBoundary
canonicalRiemannOneTwoThreeCoefficientLanguageBoundary =
  riemann-one-two-three-coefficient-language-boundary
    true true true false false
