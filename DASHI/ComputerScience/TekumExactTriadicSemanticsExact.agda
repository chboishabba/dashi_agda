module DASHI.ComputerScience.TekumExactTriadicSemanticsExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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
-- The signed fraction numerator remains explicit; no ambient real completion
-- is required at this representation layer.

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
    exactRationalNormalisationProvedHere : Bool

canonicalExactTriadicBoundary : ExactTriadicBoundary
canonicalExactTriadicBoundary =
  exactTriadicBoundary true true true false
