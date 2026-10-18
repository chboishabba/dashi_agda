module DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact where

------------------------------------------------------------------------
-- p=2 BALANCED-TERNARY NORMAL FORM:
--   1 + 1 + (3^2 - 1) = 3^2 + 1 = 10
--
-- DASHI CONTRIBUTION
--
-- The current p=2 F4-shaped target marking has fibre profile 1+1+8.
-- This module identifies the eight-state conjugate fibre exactly with the
-- punctured balanced-ternary nine-sheet T^2 \ {(0,0)}.
--
-- Therefore the whole ten-state target is an exact "duplicated centre"
-- completion of one nine-sheet:
--
--   lower centre
--   upper centre
--   eight nonzero T^2 points.
--
-- Collapsing only the duplicated centre gives back the ordinary nine-sheet.
-- This is the balanced-ternary form
--
--   10 = 1 + 1 + (3^2 - 1) = 3^2 + 1.
--
-- No arithmetic Gaussian-CM identification is claimed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.OggSSPP2F4AntipodalStratifiedRefinementExact as Stratified
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. The eight nonzero points of the balanced-ternary plane T^2.
------------------------------------------------------------------------

data PuncturedNineSheet : Set where
  negativeFirstAxis : PuncturedNineSheet
  positiveFirstAxis : PuncturedNineSheet
  negativeSecondAxis : PuncturedNineSheet
  positiveSecondAxis : PuncturedNineSheet
  negativeEqualDiagonal : PuncturedNineSheet
  positiveEqualDiagonal : PuncturedNineSheet
  negativeOppositeDiagonal : PuncturedNineSheet
  positiveOppositeDiagonal : PuncturedNineSheet

puncturedToNineSheet :
  PuncturedNineSheet ->
  Triadic.NineSheet
puncturedToNineSheet negativeFirstAxis =
  Triadic.negativeTrit , Triadic.zeroTrit
puncturedToNineSheet positiveFirstAxis =
  Triadic.positiveTrit , Triadic.zeroTrit
puncturedToNineSheet negativeSecondAxis =
  Triadic.zeroTrit , Triadic.negativeTrit
puncturedToNineSheet positiveSecondAxis =
  Triadic.zeroTrit , Triadic.positiveTrit
puncturedToNineSheet negativeEqualDiagonal =
  Triadic.negativeTrit , Triadic.negativeTrit
puncturedToNineSheet positiveEqualDiagonal =
  Triadic.positiveTrit , Triadic.positiveTrit
puncturedToNineSheet negativeOppositeDiagonal =
  Triadic.negativeTrit , Triadic.positiveTrit
puncturedToNineSheet positiveOppositeDiagonal =
  Triadic.positiveTrit , Triadic.negativeTrit

data NineSheetIsZero : Triadic.NineSheet -> Set where
  nineSheetIsZero :
    NineSheetIsZero (Triadic.zeroTrit , Triadic.zeroTrit)

puncturedPointIsNotZero :
  (point : PuncturedNineSheet) ->
  NineSheetIsZero (puncturedToNineSheet point) ->
  ⊥
puncturedPointIsNotZero negativeFirstAxis ()
puncturedPointIsNotZero positiveFirstAxis ()
puncturedPointIsNotZero negativeSecondAxis ()
puncturedPointIsNotZero positiveSecondAxis ()
puncturedPointIsNotZero negativeEqualDiagonal ()
puncturedPointIsNotZero positiveEqualDiagonal ()
puncturedPointIsNotZero negativeOppositeDiagonal ()
puncturedPointIsNotZero positiveOppositeDiagonal ()

puncturedNineSheetCount : Nat
puncturedNineSheetCount = 8

puncturedNineSheetCountIsThreeSquaredMinusOne :
  puncturedNineSheetCount ≡ 3 * 3 - 1
puncturedNineSheetCountIsThreeSquaredMinusOne = refl

------------------------------------------------------------------------
-- 2. Exact rechart:
--
-- StrictSignedSide x four noncentral antipodal classes
--   ~= punctured T^2.
------------------------------------------------------------------------

conjugateMarkToPunctured :
  Compression.StrictSignedSide × Stratified.NoncentralNineOrbit ->
  PuncturedNineSheet
conjugateMarkToPunctured
  (Compression.lowerSide , Stratified.firstAxisNoncentral) =
  negativeFirstAxis
conjugateMarkToPunctured
  (Compression.upperSide , Stratified.firstAxisNoncentral) =
  positiveFirstAxis
conjugateMarkToPunctured
  (Compression.lowerSide , Stratified.secondAxisNoncentral) =
  negativeSecondAxis
conjugateMarkToPunctured
  (Compression.upperSide , Stratified.secondAxisNoncentral) =
  positiveSecondAxis
conjugateMarkToPunctured
  (Compression.lowerSide , Stratified.equalSignNoncentral) =
  negativeEqualDiagonal
conjugateMarkToPunctured
  (Compression.upperSide , Stratified.equalSignNoncentral) =
  positiveEqualDiagonal
conjugateMarkToPunctured
  (Compression.lowerSide , Stratified.oppositeSignNoncentral) =
  negativeOppositeDiagonal
conjugateMarkToPunctured
  (Compression.upperSide , Stratified.oppositeSignNoncentral) =
  positiveOppositeDiagonal

puncturedToConjugateMark :
  PuncturedNineSheet ->
  Compression.StrictSignedSide × Stratified.NoncentralNineOrbit
puncturedToConjugateMark negativeFirstAxis =
  Compression.lowerSide , Stratified.firstAxisNoncentral
puncturedToConjugateMark positiveFirstAxis =
  Compression.upperSide , Stratified.firstAxisNoncentral
puncturedToConjugateMark negativeSecondAxis =
  Compression.lowerSide , Stratified.secondAxisNoncentral
puncturedToConjugateMark positiveSecondAxis =
  Compression.upperSide , Stratified.secondAxisNoncentral
puncturedToConjugateMark negativeEqualDiagonal =
  Compression.lowerSide , Stratified.equalSignNoncentral
puncturedToConjugateMark positiveEqualDiagonal =
  Compression.upperSide , Stratified.equalSignNoncentral
puncturedToConjugateMark negativeOppositeDiagonal =
  Compression.lowerSide , Stratified.oppositeSignNoncentral
puncturedToConjugateMark positiveOppositeDiagonal =
  Compression.upperSide , Stratified.oppositeSignNoncentral

conjugatePuncturedRoundTrip :
  (mark : Compression.StrictSignedSide × Stratified.NoncentralNineOrbit) ->
  puncturedToConjugateMark (conjugateMarkToPunctured mark) ≡ mark
conjugatePuncturedRoundTrip
  (Compression.lowerSide , Stratified.firstAxisNoncentral) = refl
conjugatePuncturedRoundTrip
  (Compression.upperSide , Stratified.firstAxisNoncentral) = refl
conjugatePuncturedRoundTrip
  (Compression.lowerSide , Stratified.secondAxisNoncentral) = refl
conjugatePuncturedRoundTrip
  (Compression.upperSide , Stratified.secondAxisNoncentral) = refl
conjugatePuncturedRoundTrip
  (Compression.lowerSide , Stratified.equalSignNoncentral) = refl
conjugatePuncturedRoundTrip
  (Compression.upperSide , Stratified.equalSignNoncentral) = refl
conjugatePuncturedRoundTrip
  (Compression.lowerSide , Stratified.oppositeSignNoncentral) = refl
conjugatePuncturedRoundTrip
  (Compression.upperSide , Stratified.oppositeSignNoncentral) = refl

puncturedConjugateRoundTrip :
  (point : PuncturedNineSheet) ->
  conjugateMarkToPunctured (puncturedToConjugateMark point) ≡ point
puncturedConjugateRoundTrip negativeFirstAxis = refl
puncturedConjugateRoundTrip positiveFirstAxis = refl
puncturedConjugateRoundTrip negativeSecondAxis = refl
puncturedConjugateRoundTrip positiveSecondAxis = refl
puncturedConjugateRoundTrip negativeEqualDiagonal = refl
puncturedConjugateRoundTrip positiveEqualDiagonal = refl
puncturedConjugateRoundTrip negativeOppositeDiagonal = refl
puncturedConjugateRoundTrip positiveOppositeDiagonal = refl

------------------------------------------------------------------------
-- 3. Duplicated-centre completion of the nine-sheet.
------------------------------------------------------------------------

data DuplicatedCentreNineSheet : Set where
  lowerCentre : DuplicatedCentreNineSheet
  upperCentre : DuplicatedCentreNineSheet
  puncturedPoint : PuncturedNineSheet -> DuplicatedCentreNineSheet

duplicatedCentreToStratified :
  DuplicatedCentreNineSheet ->
  Stratified.F4StratifiedTargetState
duplicatedCentreToStratified lowerCentre =
  Stratified.fixedZeroRefinement
duplicatedCentreToStratified upperCentre =
  Stratified.fixedOneRefinement
duplicatedCentreToStratified (puncturedPoint point)
  with puncturedToConjugateMark point
... | side , orbit =
  Stratified.conjugateRefinement side orbit

stratifiedToDuplicatedCentre :
  Stratified.F4StratifiedTargetState ->
  DuplicatedCentreNineSheet
stratifiedToDuplicatedCentre Stratified.fixedZeroRefinement =
  lowerCentre
stratifiedToDuplicatedCentre Stratified.fixedOneRefinement =
  upperCentre
stratifiedToDuplicatedCentre
  (Stratified.conjugateRefinement side orbit) =
  puncturedPoint (conjugateMarkToPunctured (side , orbit))

duplicatedCentreStratifiedRoundTrip :
  (state : DuplicatedCentreNineSheet) ->
  stratifiedToDuplicatedCentre (duplicatedCentreToStratified state) ≡ state
duplicatedCentreStratifiedRoundTrip lowerCentre = refl
duplicatedCentreStratifiedRoundTrip upperCentre = refl
duplicatedCentreStratifiedRoundTrip (puncturedPoint point)
  rewrite puncturedConjugateRoundTrip point = refl

stratifiedDuplicatedCentreRoundTrip :
  (state : Stratified.F4StratifiedTargetState) ->
  duplicatedCentreToStratified (stratifiedToDuplicatedCentre state) ≡ state
stratifiedDuplicatedCentreRoundTrip Stratified.fixedZeroRefinement = refl
stratifiedDuplicatedCentreRoundTrip Stratified.fixedOneRefinement = refl
stratifiedDuplicatedCentreRoundTrip
  (Stratified.conjugateRefinement side orbit)
  rewrite conjugatePuncturedRoundTrip (side , orbit) = refl

------------------------------------------------------------------------
-- 4. Collapse duplicated centre -> ordinary nine-sheet.
------------------------------------------------------------------------

collapseDuplicatedCentre :
  DuplicatedCentreNineSheet ->
  Triadic.NineSheet
collapseDuplicatedCentre lowerCentre =
  Triadic.zeroTrit , Triadic.zeroTrit
collapseDuplicatedCentre upperCentre =
  Triadic.zeroTrit , Triadic.zeroTrit
collapseDuplicatedCentre (puncturedPoint point) =
  puncturedToNineSheet point

duplicatedCentresCollapseTogether :
  collapseDuplicatedCentre lowerCentre
  ≡ collapseDuplicatedCentre upperCentre
duplicatedCentresCollapseTogether = refl

duplicatedCentreStateCount : Nat
duplicatedCentreStateCount = 10

duplicatedCentreStateCountIsOnePlusOnePlusPuncturedNine :
  duplicatedCentreStateCount ≡ 1 + 1 + puncturedNineSheetCount
duplicatedCentreStateCountIsOnePlusOnePlusPuncturedNine = refl

duplicatedCentreStateCountIsThreeSquaredPlusOne :
  duplicatedCentreStateCount ≡ 3 * 3 + 1
duplicatedCentreStateCountIsThreeSquaredPlusOne = refl

ninePlusDuplicatedCentreIsTen :
  10 ≡ 9 + 1
ninePlusDuplicatedCentreIsTen = refl

------------------------------------------------------------------------
-- 5. Balanced-ternary normal form.
------------------------------------------------------------------------

data BalancedTernaryP2NormalForm : Set where
  duplicatedZeroPlusPuncturedPlane : BalancedTernaryP2NormalForm

p2NormalForm :
  BalancedTernaryP2NormalForm
p2NormalForm =
  duplicatedZeroPlusPuncturedPlane

data EqualNumeralCreatesArithmeticCMIdentification : Set where

equalNumeralDoesNotCreateArithmeticCMIdentification :
  EqualNumeralCreatesArithmeticCMIdentification -> ⊥
equalNumeralDoesNotCreateArithmeticCMIdentification ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record P2BalancedTernaryPuncturedPlaneBoundary : Set where
  constructor p2-balanced-ternary-punctured-plane-boundary
  field
    conjugateFibreIsExactlyPuncturedTernaryPlane : Bool
    puncturedPlaneHasEightStates : Bool
    eightIsThreeSquaredMinusOne : Bool
    wholeTargetIsDuplicatedCentreNineSheet : Bool
    tenIsThreeSquaredPlusOne : Bool
    collapsingDuplicatedCentreGivesNineSheet : Bool
    arithmeticCMIdentificationClaimed : Bool

canonicalP2BalancedTernaryPuncturedPlaneBoundary :
  P2BalancedTernaryPuncturedPlaneBoundary
canonicalP2BalancedTernaryPuncturedPlaneBoundary =
  p2-balanced-ternary-punctured-plane-boundary
    true true true true true true false
