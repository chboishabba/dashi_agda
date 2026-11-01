module DASHI.Foundations.TernaryGolay.SelfDualityFiniteBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_+_)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.TernaryGolay.CodeBoundary as Boundary
import DASHI.Foundations.TernaryGolay.ExplicitCode729 as Explicit
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Reusable half-dimensional self-orthogonality theorem surface.
--
-- The current explicit vector API does not yet expose rowSpan/dual/dimension
-- as first-class subspaces.  This module isolates precisely the generic
-- finite-linear-algebra bridge needed to turn the already closed injectivity
-- and zero-Gram computations into an ambient self-duality theorem.
------------------------------------------------------------------------

record FiniteDualityInterface : Set₁ where
  field
    Subspace : Set
    _⊆_ : Subspace → Subspace → Set
    _≈_ : Subspace → Subspace → Set
    dual : Subspace → Subspace
    dimension : Subspace → Nat
    ambientDimension : Nat

    equalFromMutualInclusion :
      ∀ {left right} →
      left ⊆ right →
      right ⊆ left →
      left ≈ right

    halfDimensionalSelfOrthogonalIsMaximal :
      (code : Subspace) →
      code ⊆ dual code →
      dimension code + dimension code ≡ ambientDimension →
      dual code ⊆ code

open FiniteDualityInterface public

selfDualFromHalfDimension :
  (interface : FiniteDualityInterface) →
  (code : Subspace interface) →
  _⊆_ interface code (dual interface code) →
  dimension interface code + dimension interface code
    ≡ ambientDimension interface →
  _≈_ interface code (dual interface code)
selfDualFromHalfDimension interface code selfOrthogonal halfDimension =
  equalFromMutualInclusion interface
    selfOrthogonal
    (halfDimensionalSelfOrthogonalIsMaximal interface
      code selfOrthogonal halfDimension)

------------------------------------------------------------------------
-- Local finite hypotheses for the explicit code.
------------------------------------------------------------------------

orthogonalToGeneratorRows : Boundary.Word12 → Bool
orthogonalToGeneratorRows codeword =
  Explicit.rowOrthogonalToAll codeword Explicit.generatorRows

allCodewordsOrthogonalToGeneratorsCheck : Bool
allCodewordsOrthogonalToGeneratorsCheck =
  Explicit.allList
    orthogonalToGeneratorRows
    Explicit.allCodewords

allCodewordsOrthogonalToGenerators :
  allCodewordsOrthogonalToGeneratorsCheck ≡ true
allCodewordsOrthogonalToGenerators = refl

halfAmbientDimensionArithmetic : 6 + 6 ≡ 12
halfAmbientDimensionArithmetic = refl

record ExplicitSelfDualityReadiness : Set where
  constructor explicitSelfDualityReadiness
  field
    sourceAuthor : String
    sourceTitle : String
    sourceDOI : String
    systematicEncoderInjective :
      ∀ {left right : Boundary.Message6} →
      Explicit.encode left ≡ Explicit.encode right →
      left ≡ right
    generatorGramZero :
      Explicit.gramZeroCheck Explicit.generatorRows ≡ true
    everyEnumeratedCodewordOrthogonalToGenerators :
      allCodewordsOrthogonalToGeneratorsCheck ≡ true
    codeDimension : Nat
    codeDimensionIsSix : codeDimension ≡ 6
    ambientDimension : Nat
    ambientDimensionIsTwelve : ambientDimension ≡ 12
    halfDimensionArithmetic : 6 + 6 ≡ 12
    genericHalfDimensionTheoremExposed : Bool
    genericHalfDimensionTheoremExposedIsTrue :
      genericHalfDimensionTheoremExposed ≡ true
    concreteRowSpanDualBridgeInCurrentVectorAPI : Bool
    concreteRowSpanDualBridgeInCurrentVectorAPIIsFalse :
      concreteRowSpanDualBridgeInCurrentVectorAPI ≡ false

canonicalExplicitSelfDualityReadiness :
  ExplicitSelfDualityReadiness
canonicalExplicitSelfDualityReadiness =
  explicitSelfDualityReadiness
    (Sources.author Sources.macWilliamsSloaneEntry)
    (Sources.title Sources.macWilliamsSloaneEntry)
    "no DOI recorded for the cited book"
    Explicit.encodeInjective
    Explicit.generatorGramIsZero
    allCodewordsOrthogonalToGenerators
    6 refl
    12 refl
    halfAmbientDimensionArithmetic
    true refl
    false refl

selfDualityFiniteBoundaryReceipt : GenericReceipt.GenericReceipt
selfDualityFiniteBoundaryReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "finite half-dimensional self-duality bridge"
    "DASHI.Foundations.TernaryGolay.SelfDualityFiniteBoundary"
    "canonicalExplicitSelfDualityReadiness"
    "the generic half-dimensional self-orthogonal-to-self-dual theorem is isolated, and the explicit code supplies injectivity, zero Gram, all-codeword generator orthogonality and 6+6=12 arithmetic"
    "the ad hoc Vec12 API still lacks a first-class rowSpan/dual/dimension bridge, so the ambient subspace equality is not falsely reported as already kernel-instantiated"
    "agda -i . DASHI/Foundations/TernaryGolay/SelfDualityFiniteBoundary.agda"

selfDualityFiniteBoundaryReceiptNonPromoting :
  GenericReceipt.promotesClaim selfDualityFiniteBoundaryReceipt ≡ false
selfDualityFiniteBoundaryReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse selfDualityFiniteBoundaryReceipt
