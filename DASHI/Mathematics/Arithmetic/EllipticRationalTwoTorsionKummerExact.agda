module DASHI.Mathematics.Arithmetic.EllipticRationalTwoTorsionKummerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _+_; -_; ≢-nonZero)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Arithmetic.EllipticCurveTwoTorsionAndBadPrimeExact as Torsion
import DASHI.Mathematics.Arithmetic.EllipticCurveFiniteTwoDescentSeedExact as Seed
import DASHI.Mathematics.Arithmetic.RationalSquareClassSetoidExact as Square
import DASHI.Mathematics.Arithmetic.EllipticRationalKummerOpenExact as Open

two : ℚ
two = 1ℚ + 1ℚ

minusOne : ℚ
minusOne = - 1ℚ

minusTwo : ℚ
minusTwo = - two

oneNZ : Square.NonzeroRational
oneNZ = Square.nonzero-rational 1ℚ (≢-nonZero (λ ()))

minusOneNZ : Square.NonzeroRational
minusOneNZ = Square.nonzero-rational minusOne (≢-nonZero (λ ()))

twoNZ : Square.NonzeroRational
twoNZ = Square.nonzero-rational two (≢-nonZero (λ ()))

minusTwoNZ : Square.NonzeroRational
minusTwoNZ = Square.nonzero-rational minusTwo (≢-nonZero (λ ()))

torsionKummerRepresentative :
  Torsion.TwoTorsionCode →
  Open.RationalSquareClassPairRepresentative
torsionKummerRepresentative Torsion.pointAtInfinityCode =
  Open.square-class-pair-representative oneNZ oneNZ
torsionKummerRepresentative Torsion.pointZeroCode =
  Open.square-class-pair-representative minusOneNZ minusOneNZ
torsionKummerRepresentative Torsion.pointOneCode =
  Open.square-class-pair-representative oneNZ twoNZ
torsionKummerRepresentative Torsion.pointMinusOneCode =
  Open.square-class-pair-representative minusOneNZ minusTwoNZ

pointAtInfinityKummer :
  torsionKummerRepresentative Torsion.pointAtInfinityCode
  ≡ Open.square-class-pair-representative oneNZ oneNZ
pointAtInfinityKummer = refl

pointZeroKummer :
  torsionKummerRepresentative Torsion.pointZeroCode
  ≡ Open.square-class-pair-representative minusOneNZ minusOneNZ
pointZeroKummer = refl

pointOneKummer :
  torsionKummerRepresentative Torsion.pointOneCode
  ≡ Open.square-class-pair-representative oneNZ twoNZ
pointOneKummer = refl

pointMinusOneKummer :
  torsionKummerRepresentative Torsion.pointMinusOneCode
  ≡ Open.square-class-pair-representative minusOneNZ minusTwoNZ
pointMinusOneKummer = refl

torsionFiniteProjection :
  Torsion.TwoTorsionCode →
  Seed.SquareClassPair
torsionFiniteProjection =
  Seed.finiteKummerMap

torsionFiniteProjectionAgreesWithSeed :
  ∀ code →
  torsionFiniteProjection code
  ≡ Seed.finiteKummerMap code
torsionFiniteProjectionAgreesWithSeed code = refl

record LiteralTorsionKummerDictionaryEntry
    (code : Torsion.TwoTorsionCode) : Set where
  field
    representative :
      Open.RationalSquareClassPairRepresentative

    representativeExact :
      representative
      ≡ torsionKummerRepresentative code

    finiteProjection :
      Seed.SquareClassPair

    finiteProjectionExact :
      finiteProjection
      ≡ Seed.finiteKummerMap code

canonicalTorsionKummerDictionaryEntry :
  (code : Torsion.TwoTorsionCode) →
  LiteralTorsionKummerDictionaryEntry code
canonicalTorsionKummerDictionaryEntry code = record
  { representative =
      torsionKummerRepresentative code
  ; representativeExact =
      refl
  ; finiteProjection =
      torsionFiniteProjection code
  ; finiteProjectionExact =
      torsionFiniteProjectionAgreesWithSeed code
  }

record EllipticRationalTwoTorsionKummerBoundary : Set where
  constructor elliptic-rational-two-torsion-kummer-boundary
  field
    infinitySpecialValuePaid : Bool
    zeroSpecialValuePaid : Bool
    oneSpecialValuePaid : Bool
    minusOneLiteralValuePaid : Bool
    literalTwoTorsionKummerDictionaryPaid : Bool
    finiteSeedDictionaryCompatibilityPaid : Bool
    squareClassProjectionDerivedArithmeticallyPaid : Bool
    localKummerMapsPaid : Bool
    selmerGroupPaid : Bool
    bsdRankEqualityPaid : Bool

canonicalEllipticRationalTwoTorsionKummerBoundary :
  EllipticRationalTwoTorsionKummerBoundary
canonicalEllipticRationalTwoTorsionKummerBoundary =
  elliptic-rational-two-torsion-kummer-boundary
    true true true true true true false false false false
