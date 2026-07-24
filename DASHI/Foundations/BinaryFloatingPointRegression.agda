module DASHI.Foundations.BinaryFloatingPointRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.BinaryFloatingPoint

------------------------------------------------------------------------
-- Literal word decoding
------------------------------------------------------------------------

binaryThirteen : Word 4
binaryThirteen = bit1 ∷ bit1 ∷ bit0 ∷ bit1 ∷ []

binaryThirteenValue : wordValue binaryThirteen ≡ 13
binaryThirteenValue = refl

------------------------------------------------------------------------
-- The scientific-notation example 1.101₂ × 2³.
--
-- The local refinement 101₂ is 5 at depth 3, so the normalized numerator is
-- 2³ + 5 = 13.  The scale difference 3 - 3 is zero, hence the exact dyadic is
-- 13 × 2⁰.
------------------------------------------------------------------------

thirteenAddress : DyadicAddress
thirteenAddress = dyadicAddress bit0 3 5 3

thirteenDecode : ExactDyadic
thirteenDecode = normalDecode 0 thirteenAddress

thirteenDecodeNumerator :
  significandNumerator thirteenDecode ≡ 13
thirteenDecodeNumerator = refl

thirteenDecodePositiveScale :
  positivePart (scale thirteenDecode) ≡ 3
thirteenDecodePositiveScale = refl

thirteenDecodeNegativeScale :
  negativePart (scale thirteenDecode) ≡ 3
thirteenDecodeNegativeScale = refl

------------------------------------------------------------------------
-- Concrete BF16 bit pattern for +1.0:
--
--   sign     = 0
--   exponent = 01111111₂ = 127
--   fraction = 0000000₂ = 0
------------------------------------------------------------------------

bf16OneExponent : Word 8
bf16OneExponent =
  bit0 ∷ bit1 ∷ bit1 ∷ bit1 ∷
  bit1 ∷ bit1 ∷ bit1 ∷ bit1 ∷ []

bf16ZeroFraction : Word 7
bf16ZeroFraction =
  bit0 ∷ bit0 ∷ bit0 ∷ bit0 ∷
  bit0 ∷ bit0 ∷ bit0 ∷ []

bf16OneBits : BF16Bits
bf16OneBits =
  binaryFloatBits bit0 bf16OneExponent bf16ZeroFraction

bf16OneExponentValue :
  biasedScaleAddress (bf16Address bf16OneBits) ≡ 127
bf16OneExponentValue = refl

bf16OneFractionValue :
  fractionAddress (bf16Address bf16OneBits) ≡ 0
bf16OneFractionValue = refl

bf16OneNumerator :
  significandNumerator (bf16NormalDecode bf16OneBits) ≡ 128
bf16OneNumerator = refl

bf16OnePositiveScale :
  positivePart (scale (bf16NormalDecode bf16OneBits)) ≡ 127
bf16OnePositiveScale = refl

bf16OneNegativeScale :
  negativePart (scale (bf16NormalDecode bf16OneBits)) ≡ 134
bf16OneNegativeScale = refl

------------------------------------------------------------------------
-- Structural separation regressions
------------------------------------------------------------------------

bf16BinaryWitness : BinaryFormat bf16Format
bf16BinaryWitness = refl

bf16FloatingWitness : FloatingFormat bf16Format
bf16FloatingWitness = refl

bf16JointWitness : BinaryFloatingFormat bf16Format
bf16JointWitness = refl , refl

bf16KernelLocalBits :
  FloatStructuralKernel.localRefinementBits bf16StructuralKernel ≡ 7
bf16KernelLocalBits = refl

bf16KernelScaleBits :
  FloatStructuralKernel.explicitScaleBits bf16StructuralKernel ≡ 8
bf16KernelScaleBits = refl
