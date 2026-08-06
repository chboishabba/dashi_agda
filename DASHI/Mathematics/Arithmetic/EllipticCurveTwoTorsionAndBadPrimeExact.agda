module DASHI.Mathematics.Arithmetic.EllipticCurveTwoTorsionAndBadPrimeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", second edition.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- DASHI CONTRIBUTION
--
-- Add concrete rational arithmetic for E : y^2=x^3-x.  The three affine
-- points
--
--   (0,0), (1,0), (-1,0)
--
-- are checked directly on the curve.  Together with the point at infinity,
-- their two-torsion table is represented exactly by C2 x C2 and all group
-- laws are proved from Boolean xor.  The discriminant magnitude 64 is also
-- reduced to 2^6, making 2 the explicit bad-prime support candidate while the
-- selected odd primes 3,5,7,11,13,17,19 are separated from it.
--
-- Identification of the xor table with the geometric chord-and-tangent group
-- law, the minimal model, conductor exponent at 2, descent and complete
-- Mordell--Weil rank remain separate arithmetic obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≢_)

record RationalAffinePointOnCurve : Set where
  constructor affinePoint
  field
    xCoordinate yCoordinate : ℚ
    liesOnCurve :
      yCoordinate * yCoordinate
      ≡ xCoordinate * xCoordinate * xCoordinate - xCoordinate

open RationalAffinePointOnCurve public

pointZero : RationalAffinePointOnCurve
pointZero = affinePoint 0ℚ 0ℚ (solve [])

pointOne : RationalAffinePointOnCurve
pointOne = affinePoint 1ℚ 0ℚ (solve [])

pointMinusOne : RationalAffinePointOnCurve
pointMinusOne = affinePoint (- 1ℚ) 0ℚ (solve [])

pointZeroChecked :
  yCoordinate pointZero * yCoordinate pointZero
  ≡ xCoordinate pointZero * xCoordinate pointZero * xCoordinate pointZero
    - xCoordinate pointZero
pointZeroChecked = liesOnCurve pointZero

pointOneChecked :
  yCoordinate pointOne * yCoordinate pointOne
  ≡ xCoordinate pointOne * xCoordinate pointOne * xCoordinate pointOne
    - xCoordinate pointOne
pointOneChecked = liesOnCurve pointOne

pointMinusOneChecked :
  yCoordinate pointMinusOne * yCoordinate pointMinusOne
  ≡ xCoordinate pointMinusOne * xCoordinate pointMinusOne
      * xCoordinate pointMinusOne
    - xCoordinate pointMinusOne
pointMinusOneChecked = liesOnCurve pointMinusOne

------------------------------------------------------------------------
-- C2 x C2 two-torsion table.
------------------------------------------------------------------------

data Bit : Set where
  bit0 bit1 : Bit

xor : Bit → Bit → Bit
xor bit0 right = right
xor bit1 bit0 = bit1
xor bit1 bit1 = bit0

xorIdentityLeft : ∀ bit → xor bit0 bit ≡ bit
xorIdentityLeft bit0 = refl
xorIdentityLeft bit1 = refl

xorIdentityRight : ∀ bit → xor bit bit0 ≡ bit
xorIdentityRight bit0 = refl
xorIdentityRight bit1 = refl

xorSelf : ∀ bit → xor bit bit ≡ bit0
xorSelf bit0 = refl
xorSelf bit1 = refl

xorCommutative : ∀ left right → xor left right ≡ xor right left
xorCommutative bit0 bit0 = refl
xorCommutative bit0 bit1 = refl
xorCommutative bit1 bit0 = refl
xorCommutative bit1 bit1 = refl

xorAssociative : ∀ first second third →
  xor (xor first second) third ≡ xor first (xor second third)
xorAssociative bit0 bit0 bit0 = refl
xorAssociative bit0 bit0 bit1 = refl
xorAssociative bit0 bit1 bit0 = refl
xorAssociative bit0 bit1 bit1 = refl
xorAssociative bit1 bit0 bit0 = refl
xorAssociative bit1 bit0 bit1 = refl
xorAssociative bit1 bit1 bit0 = refl
xorAssociative bit1 bit1 bit1 = refl

record TwoTorsionCode : Set where
  constructor torsionCode
  field
    firstBit secondBit : Bit

open TwoTorsionCode public

torsionExtensionality : ∀ {left right} →
  firstBit left ≡ firstBit right →
  secondBit left ≡ secondBit right →
  left ≡ right
torsionExtensionality {torsionCode _ _} {torsionCode _ _} refl refl = refl

pointAtInfinityCode : TwoTorsionCode
pointAtInfinityCode = torsionCode bit0 bit0

pointZeroCode : TwoTorsionCode
pointZeroCode = torsionCode bit1 bit0

pointOneCode : TwoTorsionCode
pointOneCode = torsionCode bit0 bit1

pointMinusOneCode : TwoTorsionCode
pointMinusOneCode = torsionCode bit1 bit1

addTorsion : TwoTorsionCode → TwoTorsionCode → TwoTorsionCode
addTorsion (torsionCode a b) (torsionCode c d) =
  torsionCode (xor a c) (xor b d)

torsionIdentityLeft : ∀ point →
  addTorsion pointAtInfinityCode point ≡ point
torsionIdentityLeft (torsionCode a b) =
  torsionExtensionality (xorIdentityLeft a) (xorIdentityLeft b)

torsionIdentityRight : ∀ point →
  addTorsion point pointAtInfinityCode ≡ point
torsionIdentityRight (torsionCode a b) =
  torsionExtensionality (xorIdentityRight a) (xorIdentityRight b)

everyTorsionPointHasOrderTwo : ∀ point →
  addTorsion point point ≡ pointAtInfinityCode
everyTorsionPointHasOrderTwo (torsionCode a b) =
  torsionExtensionality (xorSelf a) (xorSelf b)

torsionAdditionCommutative : ∀ left right →
  addTorsion left right ≡ addTorsion right left
torsionAdditionCommutative (torsionCode a b) (torsionCode c d) =
  torsionExtensionality (xorCommutative a c) (xorCommutative b d)

torsionAdditionAssociative : ∀ first second third →
  addTorsion (addTorsion first second) third
  ≡ addTorsion first (addTorsion second third)
torsionAdditionAssociative
    (torsionCode a b) (torsionCode c d) (torsionCode e f) =
  torsionExtensionality
    (xorAssociative a c e)
    (xorAssociative b d f)

pointZeroPlusPointOne :
  addTorsion pointZeroCode pointOneCode ≡ pointMinusOneCode
pointZeroPlusPointOne = refl

------------------------------------------------------------------------
-- Discriminant support and selected good-prime separation.
------------------------------------------------------------------------

twoPowerSix : Nat
twoPowerSix = 2 * 2 * 2 * 2 * 2 * 2

discriminantMagnitudeIsTwoPowerSix : twoPowerSix ≡ 64
discriminantMagnitudeIsTwoPowerSix = refl

data SelectedOddPrime : Set where
  prime3 prime5 prime7 prime11 prime13 prime17 prime19 : SelectedOddPrime

selectedPrimeValue : SelectedOddPrime → Nat
selectedPrimeValue prime3 = 3
selectedPrimeValue prime5 = 5
selectedPrimeValue prime7 = 7
selectedPrimeValue prime11 = 11
selectedPrimeValue prime13 = 13
selectedPrimeValue prime17 = 17
selectedPrimeValue prime19 = 19

selectedPrimeIsNotTwo : ∀ prime → selectedPrimeValue prime ≢ 2
selectedPrimeIsNotTwo prime3 ()
selectedPrimeIsNotTwo prime5 ()
selectedPrimeIsNotTwo prime7 ()
selectedPrimeIsNotTwo prime11 ()
selectedPrimeIsNotTwo prime13 ()
selectedPrimeIsNotTwo prime17 ()
selectedPrimeIsNotTwo prime19 ()

selectedOddPrimes : List SelectedOddPrime
selectedOddPrimes =
  prime3 ∷ prime5 ∷ prime7 ∷ prime11 ∷ prime13 ∷ prime17 ∷ prime19 ∷ []

record EllipticTwoTorsionCertificate : Set where
  field
    zeroPointOnCurve : liesOnCurve pointZero
    onePointOnCurve : liesOnCurve pointOne
    minusOnePointOnCurve : liesOnCurve pointMinusOne
    groupAssociative : ∀ first second third →
      addTorsion (addTorsion first second) third
      ≡ addTorsion first (addTorsion second third)
    everyPointTwoTorsion : ∀ point →
      addTorsion point point ≡ pointAtInfinityCode
    selectedPrimesAvoidTwo : ∀ prime → selectedPrimeValue prime ≢ 2

canonicalEllipticTwoTorsionCertificate : EllipticTwoTorsionCertificate
canonicalEllipticTwoTorsionCertificate = record
  { zeroPointOnCurve = pointZeroChecked
  ; onePointOnCurve = pointOneChecked
  ; minusOnePointOnCurve = pointMinusOneChecked
  ; groupAssociative = torsionAdditionAssociative
  ; everyPointTwoTorsion = everyTorsionPointHasOrderTwo
  ; selectedPrimesAvoidTwo = selectedPrimeIsNotTwo
  }

record EllipticArithmeticCompletionBoundary : Set₁ where
  field
    geometricChordTangentAgreement : Set
    fullRationalTorsionClassification : Set
    minimalIntegralModelAtTwo : Set
    conductorExponentAtTwo : Set
    rationalPointOfInfiniteOrder : Set
    mordellWeilRankLowerBound : Set
    twoDescentMap : Set
    selmerGroupComputation : Set
    shaBoundary : Set
