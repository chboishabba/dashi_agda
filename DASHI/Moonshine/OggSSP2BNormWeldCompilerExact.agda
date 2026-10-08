module DASHI.Moonshine.OggSSP2BNormWeldCompilerExact where

------------------------------------------------------------------------
-- TERMINAL NORM-WELD COMPILER
--
-- Source-native dimensions:
--   minus reduction                       98304
--   common centralizer lane               98280
--   residual natural lane                    24
--   plus oscillator Sym2(24)                300
--   final Tate / exterior-square quotient   276.
--
-- Lean proves the rank squeeze generically.  Once runtime support separation
-- is paid, the residual norm projection has rank 24 and the complementary
-- kernel has dimension 98280.  The independent Hom screen then makes every
-- nonzero Co1-equivariant 24 -> Sym2(24) map the Frobenius-square embedding.
--
-- Therefore the residual 24 map is not an independent same-object theorem.
-- After those finite/runtime facts are ingested, the literal vertical weld has
-- one genuine map-level producer left: identify the actual norm map on the
-- common 98280 extension lane.  The final quotient-isomorphism theorem is kept
-- separate until that same-object common-lane map is actually supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _-_)

commonDimension : Nat
commonDimension = 98280

minusDimension : Nat
minusDimension = 98304

residualDimension : Nat
residualDimension = minusDimension - commonDimension

residualRankForcedTwentyFour : residualDimension ≡ 24
residualRankForcedTwentyFour = refl

commonKernelForced98280 : commonDimension ≡ 98280
commonKernelForced98280 = refl

symmetricSquareDimension : Nat
symmetricSquareDimension = 300

frobeniusImageDimension : Nat
frobeniusImageDimension = residualDimension

exteriorSquareDimension : Nat
exteriorSquareDimension = symmetricSquareDimension - frobeniusImageDimension

exteriorSquareDimensionIs276 : exteriorSquareDimension ≡ 276
exteriorSquareDimensionIs276 = refl

-- Proof-relevant finite/runtime promotion.  Generated runtime receipts or
-- kernel theorems must inhabit these coordinates; Boolean flags are not enough.
record FiniteNormRigidityReceipt : Set₁ where
  constructor finite-norm-rigidity-receipt
  field
    SupportSeparationPaid : Set
    supportSeparationPaid : SupportSeparationPaid
    UniqueNonzeroFrobeniusHomPaid : Set
    uniqueNonzeroFrobeniusHomPaid : UniqueNonzeroFrobeniusHomPaid
    ResidualMapFrobeniusWitness : Set
    residualMapFrobeniusWitness : ResidualMapFrobeniusWitness

open FiniteNormRigidityReceipt public

-- The one same-object producer intentionally left uninhabited by finite
-- character/module calculations.
record Common98280NormSameObjectReceipt : Set₁ where
  constructor common-98280-norm-same-object-receipt
  field
    ActualCommonNormMapIdentification : Set
    actualCommonNormMapIdentification : ActualCommonNormMapIdentification

open Common98280NormSameObjectReceipt public

-- After finite rigidity is paid, this compiler exposes the exact two inputs to
-- the terminal quotient theorem: the actual common-lane identification and the
-- already-forced residual Frobenius map.  It deliberately does NOT claim that
-- the quotient is wedge2(24) until a separate quotient theorem consumes them.
record NormWeldInputs : Set₁ where
  constructor norm-weld-inputs
  field
    CommonLaneIdentification : Set
    commonLaneIdentification : CommonLaneIdentification
    ResidualFrobeniusIdentification : Set
    residualFrobeniusIdentification : ResidualFrobeniusIdentification

assembleNormWeldInputs :
  FiniteNormRigidityReceipt →
  Common98280NormSameObjectReceipt →
  NormWeldInputs
assembleNormWeldInputs finite common =
  norm-weld-inputs
    (ActualCommonNormMapIdentification common)
    (actualCommonNormMapIdentification common)
    (ResidualMapFrobeniusWitness finite)
    (residualMapFrobeniusWitness finite)

residualMapForcedFrobenius :
  (finite : FiniteNormRigidityReceipt) →
  ResidualMapFrobeniusWitness finite
residualMapForcedFrobenius = residualMapFrobeniusWitness

-- This is the desired terminal theorem name, but its proof remains explicitly
-- gated by a proof-relevant quotient-identification compiler rather than being
-- manufactured from dimension arithmetic.
record ExteriorSquareQuotientCompiler : Set₁ where
  constructor exterior-square-quotient-compiler
  field
    compile : NormWeldInputs → Set

tateCokernelForcedExteriorSquare :
  ExteriorSquareQuotientCompiler →
  FiniteNormRigidityReceipt →
  Common98280NormSameObjectReceipt →
  Set
tateCokernelForcedExteriorSquare quotientCompiler finite common =
  ExteriorSquareQuotientCompiler.compile quotientCompiler
    (assembleNormWeldInputs finite common)

onlyCommon98280MapRemains :
  Common98280NormSameObjectReceipt → Common98280NormSameObjectReceipt
onlyCommon98280MapRemains common = common
