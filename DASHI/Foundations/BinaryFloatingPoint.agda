module DASHI.Foundations.BinaryFloatingPoint where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _-_; _<_; _==_)

------------------------------------------------------------------------
-- Finite binary words
------------------------------------------------------------------------

data Bit : Set where
  bit0 bit1 : Bit

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_

Word : Nat → Set
Word = Vec Bit

bitValue : Bit → Nat
bitValue bit0 = 0
bitValue bit1 = 1

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 * pow2 n

wordValue : {n : Nat} → Word n → Nat
wordValue [] = 0
wordValue (b ∷ bs) = bitValue b * pow2 _ + wordValue bs

------------------------------------------------------------------------
-- Radix and scale policy are different coordinates.
------------------------------------------------------------------------

data Radix : Set where
  binaryRadix decimalRadix : Radix

data ScalePolicy : Set where
  fixedScale floatingScale : ScalePolicy

record NumericFormat : Set where
  constructor numericFormat
  field
    radix : Radix
    scalePolicy : ScalePolicy
    exponentWidth : Nat
    fractionWidth : Nat

open NumericFormat public

BinaryFormat : NumericFormat → Set
BinaryFormat format = radix format ≡ binaryRadix

FloatingFormat : NumericFormat → Set
FloatingFormat format = scalePolicy format ≡ floatingScale

BinaryFloatingFormat : NumericFormat → Set
BinaryFloatingFormat format =
  BinaryFormat format × FloatingFormat format

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    first : A
    second : B

open _×_ public

binaryAndFloatingAreCompatible :
  BinaryFloatingFormat
    (numericFormat binaryRadix floatingScale 8 7)
binaryAndFloatingAreCompatible = refl , refl

binaryDoesNotMeanFixed :
  BinaryFormat (numericFormat binaryRadix floatingScale 8 7)
binaryDoesNotMeanFixed = refl

floatingDoesNotMeanDecimal :
  FloatingFormat (numericFormat binaryRadix floatingScale 8 7)
floatingDoesNotMeanDecimal = refl

------------------------------------------------------------------------
-- Generic finite binary floating-point carrier.
------------------------------------------------------------------------

record BinaryFloatBits (exponentBits fractionBits : Nat) : Set where
  constructor binaryFloatBits
  field
    sign : Bit
    exponent : Word exponentBits
    fraction : Word fractionBits

open BinaryFloatBits public

record DyadicAddress : Set where
  constructor dyadicAddress
  field
    orientation : Bit
    biasedScaleAddress : Nat
    fractionAddress : Nat
    fractionDepth : Nat

open DyadicAddress public

address :
  {exponentBits fractionBits : Nat} →
  BinaryFloatBits exponentBits fractionBits →
  DyadicAddress
address {fractionBits = fractionBits} bits =
  dyadicAddress
    (sign bits)
    (wordValue (exponent bits))
    (wordValue (fraction bits))
    fractionBits

------------------------------------------------------------------------
-- Exact symbolic decode for normal values.
--
-- The represented magnitude is
--
--   (2^fractionDepth + fractionAddress)
--     * 2^(biasedScaleAddress - bias - fractionDepth).
--
-- Keeping the signed scale as a difference avoids importing an ambient real
-- number system while retaining the exact dyadic value.
------------------------------------------------------------------------

record SignedScale : Set where
  constructor signedScale
  field
    positivePart : Nat
    negativePart : Nat

open SignedScale public

record ExactDyadic : Set where
  constructor exactDyadic
  field
    dyadicSign : Bit
    significandNumerator : Nat
    scale : SignedScale

open ExactDyadic public

normalDecode :
  (bias : Nat) →
  DyadicAddress →
  ExactDyadic
normalDecode bias a =
  exactDyadic
    (orientation a)
    (pow2 (fractionDepth a) + fractionAddress a)
    (signedScale
      (biasedScaleAddress a)
      (bias + fractionDepth a))

------------------------------------------------------------------------
-- Fixed-point and floating-point are separated by scale ownership.
------------------------------------------------------------------------

record FixedBinary (fractionDepth : Nat) : Set where
  constructor fixedBinary
  field
    fixedSign : Bit
    fixedNumerator : Nat

record FloatingBinary (exponentBits fractionBits : Nat) : Set where
  constructor floatingBinary
  field
    floatingBits : BinaryFloatBits exponentBits fractionBits

fixedScaleIsExternal :
  {fractionDepth : Nat} →
  FixedBinary fractionDepth →
  Nat
fixedScaleIsExternal {fractionDepth} value = fractionDepth

floatingScaleIsStored :
  {exponentBits fractionBits : Nat} →
  FloatingBinary exponentBits fractionBits →
  Nat
floatingScaleIsStored value =
  biasedScaleAddress (address (floatingBits value))

------------------------------------------------------------------------
-- BF16
------------------------------------------------------------------------

bf16Format : NumericFormat
bf16Format = numericFormat binaryRadix floatingScale 8 7

bf16IsBinaryFloating : BinaryFloatingFormat bf16Format
bf16IsBinaryFloating = refl , refl

BF16Bits : Set
BF16Bits = BinaryFloatBits 8 7

bf16ExponentBias : Nat
bf16ExponentBias = 127

bf16Address : BF16Bits → DyadicAddress
bf16Address = address

bf16NormalDecode : BF16Bits → ExactDyadic
bf16NormalDecode bits = normalDecode bf16ExponentBias (bf16Address bits)

bf16ExponentWidth : exponentWidth bf16Format ≡ 8
bf16ExponentWidth = refl

bf16FractionWidth : fractionWidth bf16Format ≡ 7
bf16FractionWidth = refl

------------------------------------------------------------------------
-- DASHI reading boundary.
------------------------------------------------------------------------

data CoordinateRole : Set where
  orientationRole localRefinementRole scaleTransportRole : CoordinateRole

bf16SignRole : CoordinateRole
bf16SignRole = orientationRole

bf16FractionRole : CoordinateRole
bf16FractionRole = localRefinementRole

bf16ExponentRole : CoordinateRole
bf16ExponentRole = scaleTransportRole

record FloatStructuralKernel : Set where
  constructor floatStructuralKernel
  field
    localRefinementBits : Nat
    explicitScaleBits : Nat
    localRole : CoordinateRole
    scaleRole : CoordinateRole

bf16StructuralKernel : FloatStructuralKernel
bf16StructuralKernel =
  floatStructuralKernel
    7
    8
    localRefinementRole
    scaleTransportRole

radixIsNotScalePolicy :
  (radix bf16Format ≡ binaryRadix) ×
  (scalePolicy bf16Format ≡ floatingScale)
radixIsNotScalePolicy = refl , refl
