module DASHI.ComputerScience.TekumExactTriadicSemanticsExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _+_; _*_; -_)
import Data.Integer.Properties as ℤP
open import Data.Rational.Base using (ℚ; normalize)

import DASHI.Foundations.BinaryFloatingPoint as Binary
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem

------------------------------------------------------------------------
-- Radix-3 analogue of BinaryFloatingPoint.ExactDyadic.
--
-- For ordinary Tekum data
--
--   s (1 + F / 3^p) 3^e
--
-- the exact magnitude can be carried without machine Float as
--
--   s (3^p + F) 3^(e-p).
--
-- The symbolic carrier below reuses BinaryFloatingPoint.SignedScale; the
-- second half of this owner gives the corresponding canonical ℚ value.

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

record ExactSignedNumerator : Set where
  constructor exactSignedNumerator
  field
    baseUnit : Nat
    adjustment : Sem.IntCode
open ExactSignedNumerator public

record ExactTriadic : Set where
  constructor exactTriadic
  field
    triadicSign : Anchor.TekumSign
    significand : ExactSignedNumerator
    scale : Binary.SignedScale
open ExactTriadic public

intCodeScale : Sem.IntCode → Nat → Binary.SignedScale
intCodeScale (Sem.nonnegative e) p =
  Binary.signedScale e p
intCodeScale (Sem.negative e) p =
  Binary.signedScale 0 (e + p)

ordinaryExactTriadic : Sem.OrdinaryTekum → ExactTriadic
ordinaryExactTriadic x =
  exactTriadic
    (Sem.sign x)
    (exactSignedNumerator
      (pow3 (Sem.fractionTritCount x))
      (Sem.fractionNumerator x))
    (intCodeScale
      (Sem.exponent x)
      (Sem.fractionTritCount x))

------------------------------------------------------------------------
-- Canonical rational semantics for ordinary finite values.

intCodeToInteger : Sem.IntCode → ℤ
intCodeToInteger (Sem.nonnegative n) = + n
intCodeToInteger (Sem.negative zero) = + 0
intCodeToInteger (Sem.negative (suc n)) = -[1+ n ]

applySign : Anchor.TekumSign → ℤ → ℤ
applySign Anchor.negativeSign z = - z
applySign Anchor.zeroSign z = + 0
applySign Anchor.positiveSign z = z

applySignFlip :
  (s : Anchor.TekumSign) (z : ℤ) →
  applySign (Anchor.flipSign s) z ≡ ℤ.- (applySign s z)
applySignFlip Anchor.negativeSign z = ℤP.neg-involutive z
applySignFlip Anchor.zeroSign z = refl
applySignFlip Anchor.positiveSign z = refl

flipExactTriadicSign : ExactTriadic → ExactTriadic
flipExactTriadicSign x =
  exactTriadic
    (Anchor.flipSign (triadicSign x))
    (significand x)
    (scale x)

exactTriadicNumerator : ExactTriadic → ℤ
exactTriadicNumerator x =
  applySign
    (triadicSign x)
    (((+ (baseUnit (significand x)))
       ℤ.+ intCodeToInteger (adjustment (significand x)))
      ℤ.* (+ (pow3 (Binary.positivePart (scale x)))))

exactTriadicDenominator : ExactTriadic → Nat
exactTriadicDenominator x =
  pow3 (Binary.negativePart (scale x))

flipExactTriadicDenominatorInvariant :
  (x : ExactTriadic) →
  exactTriadicDenominator (flipExactTriadicSign x)
  ≡ exactTriadicDenominator x
flipExactTriadicDenominatorInvariant x = refl

exactTriadicRational : ExactTriadic → ℚ
exactTriadicRational x =
  normalize
    (exactTriadicNumerator x)
    (exactTriadicDenominator x)

ordinaryRational : Sem.OrdinaryTekum → ℚ
ordinaryRational x = exactTriadicRational (ordinaryExactTriadic x)

------------------------------------------------------------------------
-- Structural calibration rows.

zeroExponentZeroFractionDepthThree :
  ordinaryExactTriadic
    (Sem.ordinaryTekum
      Anchor.positiveSign
      (Sem.nonnegative 0)
      (Sem.nonnegative 0)
      3)
  ≡ exactTriadic
      Anchor.positiveSign
      (exactSignedNumerator 27 (Sem.nonnegative 0))
      (Binary.signedScale 0 3)
zeroExponentZeroFractionDepthThree = refl

positiveExponentTwoDepthThree :
  Binary.positivePart
    (scale
      (ordinaryExactTriadic
        (Sem.ordinaryTekum
          Anchor.positiveSign
          (Sem.nonnegative 2)
          (Sem.nonnegative 0)
          3)))
  ≡ 2
positiveExponentTwoDepthThree = refl

negativeExponentTwoDepthThree :
  Binary.negativePart
    (scale
      (ordinaryExactTriadic
        (Sem.ordinaryTekum
          Anchor.positiveSign
          (Sem.negative 2)
          (Sem.nonnegative 0)
          3)))
  ≡ 5
negativeExponentTwoDepthThree = refl

record ExactTriadicBoundary : Set where
  constructor exactTriadicBoundary
  field
    machineFloatAvoided : Bool
    sameSignedScaleOwnerAsBinaryFloatReused : Bool
    fractionDepthAbsorbedIntoScale : Bool
    canonicalRationalDecoderPresent : Bool
    naRAndInfinityForcedIntoRational : Bool

canonicalExactTriadicBoundary : ExactTriadicBoundary
canonicalExactTriadicBoundary =
  exactTriadicBoundary true true true true false
