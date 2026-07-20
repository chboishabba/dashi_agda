module DASHI.Foundations.ReflectionChartPolymorphism where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (Trit; neg; zer; pos)

------------------------------------------------------------------------
-- Decimal reflection around five.

data DecimalPhase11 : Set where
  d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 : DecimalPhase11

reflect10 : DecimalPhase11 → DecimalPhase11
reflect10 d0 = d10
reflect10 d1 = d9
reflect10 d2 = d8
reflect10 d3 = d7
reflect10 d4 = d6
reflect10 d5 = d5
reflect10 d6 = d4
reflect10 d7 = d3
reflect10 d8 = d2
reflect10 d9 = d1
reflect10 d10 = d0

reflect10-involutive : (x : DecimalPhase11) → reflect10 (reflect10 x) ≡ x
reflect10-involutive d0 = refl
reflect10-involutive d1 = refl
reflect10-involutive d2 = refl
reflect10-involutive d3 = refl
reflect10-involutive d4 = refl
reflect10-involutive d5 = refl
reflect10-involutive d6 = refl
reflect10-involutive d7 = refl
reflect10-involutive d8 = refl
reflect10-involutive d9 = refl
reflect10-involutive d10 = refl

decimalFiveFixed : reflect10 d5 ≡ d5
decimalFiveFixed = refl

------------------------------------------------------------------------
-- Additive inverse on C9.  This is the chart where 3 and 6 are paired.

data Phase9 : Set where
  p0 p1 p2 p3 p4 p5 p6 p7 p8 : Phase9

reflect9 : Phase9 → Phase9
reflect9 p0 = p0
reflect9 p1 = p8
reflect9 p2 = p7
reflect9 p3 = p6
reflect9 p4 = p5
reflect9 p5 = p4
reflect9 p6 = p3
reflect9 p7 = p2
reflect9 p8 = p1

reflect9-involutive : (x : Phase9) → reflect9 (reflect9 x) ≡ x
reflect9-involutive p0 = refl
reflect9-involutive p1 = refl
reflect9-involutive p2 = refl
reflect9-involutive p3 = refl
reflect9-involutive p4 = refl
reflect9-involutive p5 = refl
reflect9-involutive p6 = refl
reflect9-involutive p7 = refl
reflect9-involutive p8 = refl

threeReflectsToSix : reflect9 p3 ≡ p6
threeReflectsToSix = refl

sixReflectsToThree : reflect9 p6 ≡ p3
sixReflectsToThree = refl

------------------------------------------------------------------------
-- Native balanced-ternary sign inversion.

tritReflection : Trit → Trit
tritReflection neg = pos
tritReflection zer = zer
tritReflection pos = neg

tritReflection-involutive : (t : Trit) → tritReflection (tritReflection t) ≡ t
tritReflection-involutive neg = refl
tritReflection-involutive zer = refl
tritReflection-involutive pos = refl

balancedZeroFixed : tritReflection zer ≡ zer
balancedZeroFixed = refl

------------------------------------------------------------------------
-- The same word "reflection" may name distinct maps.  Their consequences do
-- not transfer without a named bridge.

data ReflectionRole : Set where
  decimalComplement : ReflectionRole
  modularAdditiveInverse : ReflectionRole
  phaseReversal : ReflectionRole
  polarityFlip : ReflectionRole
  digitwiseTernaryInvolution : ReflectionRole
  chartDuality : ReflectionRole

record ReflectionChart : Set₁ where
  field
    Carrier : Set
    reflect : Carrier → Carrier
    involutive : (x : Carrier) → reflect (reflect x) ≡ x
    role : ReflectionRole
    interpretation : String

canonicalDecimalReflection : ReflectionChart
canonicalDecimalReflection =
  record
    { Carrier = DecimalPhase11
    ; reflect = reflect10
    ; involutive = reflect10-involutive
    ; role = decimalComplement
    ; interpretation = "decimal complement about the fixed midpoint five"
    }

canonicalModNineReflection : ReflectionChart
canonicalModNineReflection =
  record
    { Carrier = Phase9
    ; reflect = reflect9
    ; involutive = reflect9-involutive
    ; role = modularAdditiveInverse
    ; interpretation = "additive inverse on C9, pairing three with six"
    }

canonicalTritReflection : ReflectionChart
canonicalTritReflection =
  record
    { Carrier = Trit
    ; reflect = tritReflection
    ; involutive = tritReflection-involutive
    ; role = digitwiseTernaryInvolution
    ; interpretation = "balanced-ternary polarity inversion with zero fixed"
    }

record ReflectionPolymorphismBoundary : Set where
  constructor reflectionPolymorphismBoundary
  field
    multipleReflectionChartsAvailable : Bool
    decimalAndModNineMapsIdentical : Bool
    decimalAndModNineMapsIdenticalIsFalse : decimalAndModNineMapsIdentical ≡ false
    decimalFiveAndTritZeroSameArithmeticElement : Bool
    decimalFiveAndTritZeroSameArithmeticElementIsFalse :
      decimalFiveAndTritZeroSameArithmeticElement ≡ false
    chartBridgeMayIdentifyTheirRoles : Bool
    interpretation : String

canonicalReflectionPolymorphismBoundary : ReflectionPolymorphismBoundary
canonicalReflectionPolymorphismBoundary =
  reflectionPolymorphismBoundary
    true
    false refl
    false refl
    true
    "decimal midpoint, modular inverse, phase reversal, polarity flip, ternary involution, and chart duality coexist as typed views rather than one untyped operation"
