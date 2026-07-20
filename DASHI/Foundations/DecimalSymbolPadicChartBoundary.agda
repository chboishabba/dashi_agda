module DASHI.Foundations.DecimalSymbolPadicChartBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (Trit; neg; zer; pos)
import DASHI.Foundations.JChartSuccessorBoundary as Charts

------------------------------------------------------------------------
-- Decimal-symbol, canonical p-adic, phase, and chart readings are parallel
-- views.  They are not silently coercible into one another.

data ReadingKind : Set where
  decimalSymbolReading canonical3AdicReading phaseReading chartReading : ReadingKind

record DecimalSymbolAddress : Set where
  constructor decimalSymbolAddress
  field
    integerPart : Nat
    fractionalDigits : List Nat
    semanticReading : String

record PadicAddress : Set where
  constructor padicAddress
  field
    retainedDepth : Nat
    balancedTrits : List Trit

record ExplicitReadingBridge : Set where
  constructor explicitReadingBridge
  field
    sourceReading targetReading : ReadingKind
    bridgeName : String
    semanticsPreserved : Set

data Never : Set where

data UnmediatedReadingTransfer : ReadingKind → ReadingKind → Set where
  sameDecimal : UnmediatedReadingTransfer decimalSymbolReading decimalSymbolReading
  samePadic : UnmediatedReadingTransfer canonical3AdicReading canonical3AdicReading
  samePhase : UnmediatedReadingTransfer phaseReading phaseReading
  sameChart : UnmediatedReadingTransfer chartReading chartReading

decimalCannotBecomePadicUnmediated :
  UnmediatedReadingTransfer decimalSymbolReading canonical3AdicReading → Never
decimalCannotBecomePadicUnmediated ()

feigenbaumDecimalSymbolAddress : DecimalSymbolAddress
feigenbaumDecimalSymbolAddress =
  decimalSymbolAddress 3
    (5 ∷ 6 ∷ 9 ∷ 9 ∷ 4 ∷ 5 ∷ 6 ∷ [])
    "custom decimal-symbol chart: integer part is a promoted coarse label and the fractional tail is an unresolved candidate layer"

------------------------------------------------------------------------
-- Decimal midpoint 5 becomes zero only in an explicit centred chart.

data CentredSign : Set where
  negativeSide zeroCrossing positiveSide : CentredSign

centreAtFive : Nat → CentredSign
centreAtFive zero = negativeSide
centreAtFive (suc zero) = negativeSide
centreAtFive (suc (suc zero)) = negativeSide
centreAtFive (suc (suc (suc zero))) = negativeSide
centreAtFive (suc (suc (suc (suc zero)))) = negativeSide
centreAtFive (suc (suc (suc (suc (suc zero))))) = zeroCrossing
centreAtFive (suc (suc (suc (suc (suc (suc n)))))) = positiveSide

fiveIsCentredZero : centreAtFive 5 ≡ zeroCrossing
fiveIsCentredZero = refl

------------------------------------------------------------------------
-- Star/j normalisation, inverse, and successor roles.

record StarNormalisation : Set₁ where
  field
    Carrier : Set
    star one : Carrier
    inverse : Carrier → Carrier
    multiply : Carrier → Carrier → Carrier
    starInverseLaw : multiply (inverse star) star ≡ one
    selfNormalisationLaw : multiply (inverse star) star ≡ one

starChart : Charts.ChartIndex
starChart = Charts.chart 10

starSuccessorChart : Charts.ChartIndex
starSuccessorChart = Charts.nextChart starChart

starSuccessorIsEleven : starSuccessorChart ≡ Charts.chart 11
starSuccessorIsEleven = refl

record DecimalSymbolPadicBoundary : Set where
  constructor decimalSymbolPadicBoundary
  field
    decimalDigitsArePadicDigits : Bool
    decimalDigitsArePadicDigitsIsFalse : decimalDigitsArePadicDigits ≡ false
    decimalPointIsCanonicalPadicValuation : Bool
    decimalPointIsCanonicalPadicValuationIsFalse :
      decimalPointIsCanonicalPadicValuation ≡ false
    fiveEqualsZeroArithmetically : Bool
    fiveEqualsZeroArithmeticallyIsFalse : fiveEqualsZeroArithmetically ≡ false
    fiveMapsToZeroInCentredChart : Bool
    starOverOneEqualsOneClaimed : Bool
    starOverOneEqualsOneClaimedIsFalse : starOverOneEqualsOneClaimed ≡ false
    inverseOfStarTimesStarIsOne : Bool
    interpretation : String

canonicalDecimalSymbolPadicBoundary : DecimalSymbolPadicBoundary
canonicalDecimalSymbolPadicBoundary =
  decimalSymbolPadicBoundary
    false refl
    false refl
    false refl
    true
    false refl
    true
    "decimal-symbol readings, balanced-ternary residue readings, centred phase charts, and j/j+1 chart succession coexist only through named bridges"
