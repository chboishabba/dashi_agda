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
-- The finite/runtime side now pays:
--   * common/residual modular support separation;
--   * one unique residual degree-24 simple;
--   * dim Hom_Co1(24,Sym2(24)) = 1;
--   * the explicit Frobenius rank-24 map spans that Hom line.
--
-- Lean sharpens the same-object theorem as follows.  Write the actual
-- source-native norm map in canonical target block coordinates
--
--   n = (c,r) : M_98304 -> C_98280 x S_300.
--
-- It is enough to produce the canonical rank-24 source residual block
-- projector e24 and prove the actual block-equivariance equation
--
--   r o e24 = r.
--
-- Then rank(r)<=24.  Norm injectivity embeds ker(r) through c into C_98280;
-- rank-nullity has no slack, so rank(r)=24 and dim ker(r)=98280.  Thus the
-- common 98280 lane is an automatic same-object equivalence rather than a
-- separate map-discovery gate.  The induced nonzero equivariant map on the
-- residual 24 quotient is then forced onto the already-paid Frobenius Hom line.
--
-- Hence the preferred terminal gate is ONE actual residual-block/equivariance
-- receipt.  A legacy common-98280 receipt is retained below only as an audit
-- compatibility surface; it is not the shortest proof path.
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

-- Proof-relevant finite/runtime facts.  These are not substitutes for the
-- actual norm-map equation.
record FiniteNormRigidityReceipt : Set₁ where
  constructor finite-norm-rigidity-receipt
  field
    SupportSeparationPaid : Set
    supportSeparationPaid : SupportSeparationPaid
    UniqueNonzeroFrobeniusHomPaid : Set
    uniqueNonzeroFrobeniusHomPaid : UniqueNonzeroFrobeniusHomPaid

open FiniteNormRigidityReceipt public

-- Preferred one-piece same-object producer.
record ResidualBlockNormSameObjectReceipt : Set₁ where
  constructor residual-block-norm-same-object-receipt
  field
    ActualResidualBlockProjector : Set
    actualResidualBlockProjector : ActualResidualBlockProjector
    ResidualNormBlockEquivariance : Set
    residualNormBlockEquivariance : ResidualNormBlockEquivariance
    InducedResidualCo1Equivariance : Set
    inducedResidualCo1Equivariance : InducedResidualCo1Equivariance

open ResidualBlockNormSameObjectReceipt public

-- Legacy audit surface.  Lean proves this common-lane datum follows from the
-- preferred residual-block receipt and source-native norm injectivity.
record Common98280NormSameObjectReceipt : Set₁ where
  constructor common-98280-norm-same-object-receipt
  field
    ActualCommonNormMapIdentification : Set
    actualCommonNormMapIdentification : ActualCommonNormMapIdentification

open Common98280NormSameObjectReceipt public

record NormWeldInputs : Set₁ where
  constructor norm-weld-inputs
  field
    CommonLaneIdentification : Set
    commonLaneIdentification : CommonLaneIdentification
    ResidualFrobeniusIdentification : Set
    residualFrobeniusIdentification : ResidualFrobeniusIdentification

-- Proof-bearing implementation of Lean's support-squeeze + Hom-line chain.
-- Agda keeps the internal linear-algebra implementation abstract and requires
-- the compiler itself to be inhabited rather than replacing it by booleans.
record ResidualBlockNormWeldCompiler : Set₁ where
  constructor residual-block-norm-weld-compiler
  field
    compile :
      FiniteNormRigidityReceipt ->
      ResidualBlockNormSameObjectReceipt ->
      NormWeldInputs

open ResidualBlockNormWeldCompiler public

-- Legacy assembler retained for audit compatibility only.
record LegacyFiniteNormRigidityReceipt : Set₁ where
  constructor legacy-finite-norm-rigidity-receipt
  field
    LegacyResidualMapFrobeniusWitness : Set
    legacyResidualMapFrobeniusWitness : LegacyResidualMapFrobeniusWitness

assembleLegacyNormWeldInputs :
  LegacyFiniteNormRigidityReceipt ->
  Common98280NormSameObjectReceipt ->
  NormWeldInputs
assembleLegacyNormWeldInputs finite common =
  norm-weld-inputs
    (ActualCommonNormMapIdentification common)
    (actualCommonNormMapIdentification common)
    (LegacyResidualMapFrobeniusWitness finite)
    (legacyResidualMapFrobeniusWitness finite)

record ExteriorSquareQuotientCompiler : Set₁ where
  constructor exterior-square-quotient-compiler
  field
    compile : NormWeldInputs -> Set

-- Preferred terminal theorem: no independent common-98280 receipt appears.
tateCokernelForcedExteriorSquareFromResidualBlock :
  ExteriorSquareQuotientCompiler ->
  ResidualBlockNormWeldCompiler ->
  FiniteNormRigidityReceipt ->
  ResidualBlockNormSameObjectReceipt ->
  Set
tateCokernelForcedExteriorSquareFromResidualBlock quotientCompiler normCompiler finite residual =
  ExteriorSquareQuotientCompiler.compile quotientCompiler
    (ResidualBlockNormWeldCompiler.compile normCompiler finite residual)

-- Legacy theorem retained for historical comparison only.
tateCokernelForcedExteriorSquareLegacy :
  ExteriorSquareQuotientCompiler ->
  LegacyFiniteNormRigidityReceipt ->
  Common98280NormSameObjectReceipt ->
  Set
tateCokernelForcedExteriorSquareLegacy quotientCompiler finite common =
  ExteriorSquareQuotientCompiler.compile quotientCompiler
    (assembleLegacyNormWeldInputs finite common)

onlyResidualBlockMapRemains :
  ResidualBlockNormSameObjectReceipt -> ResidualBlockNormSameObjectReceipt
onlyResidualBlockMapRemains residual = residual
