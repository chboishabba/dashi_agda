module DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOrderedFieldCapabilityAdapter where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Herman Geuvers; Milad Niqui;
-- Zachary Murray; Viktor Csimma; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Reals in Coq: Axioms and
-- Categoricity"; "Constructive Analysis in the Agda Proof Assistant"; and
-- "Unified ordered-field capability adapter for Stage-3 output relocation".
-- Venue/year: Springer, 1985; Types for Proofs and Programs, LNCS 2277
-- (2002), 79--95; arXiv, 2022; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.1007/3-540-45842-5_6;
-- 10.48550/arXiv.2205.08354; the repository adapter has no DOI.
-- Uses: one coherent constructive ordered-field/rational-embedding package.
-- Relationship: constructs the previously separate native envelope,
-- absolute-value, nonnegative-square and strict subtraction capabilities from
-- one backend record.  This removes cross-record coherence as an implicit
-- obligation.  A concrete Fast-Cauchy/Bishop package remains fail-closed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_)

import DASHI.Analysis.ConstructiveRealSpine as Spine
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputEnvelopeAdapter as Adapter
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputRelocationDerivedClosure as Derived
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputRelocationSquaredClosure as SquaredClosure
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputDecayIntervalDerivation as Interval

record ConstructiveRealSpineOrderedFieldCapability
    (R : Spine.ConstructedOrderedCompleteReal) : Set₁ where
  field
    rationalEmbed : ℚ → Spine.Real R

    leqReflexive : ∀ value → Spine._≤_ R value value
    leqTransitive : ∀ {a b c} →
      Spine._≤_ R a b → Spine._≤_ R b c → Spine._≤_ R a c
    addMonotone : ∀ {a b c d} →
      Spine._≤_ R a b → Spine._≤_ R c d →
      Spine._≤_ R (Spine._+_ R a c) (Spine._+_ R b d)
    multiplyMonotoneNonnegative : ∀ {a b c d} →
      Spine._≤_ R (Spine.zero R) a →
      Spine._≤_ R a b →
      Spine._≤_ R (Spine.zero R) c →
      Spine._≤_ R c d →
      Spine._≤_ R (Spine._*_ R a c) (Spine._*_ R b d)
    negateAntitone : ∀ {a b} →
      Spine._≤_ R a b → Spine._≤_ R (Spine.neg R b) (Spine.neg R a)
    negateAdd : ∀ a b →
      Spine.neg R (Spine._+_ R a b)
      ≡ Spine._+_ R (Spine.neg R a) (Spine.neg R b)

    embedZero : rationalEmbed 0ℚ ≡ Spine.zero R
    embedOne : rationalEmbed 1ℚ ≡ Spine.one R
    embedAdd : ∀ left right →
      rationalEmbed (left + right)
      ≡ Spine._+_ R (rationalEmbed left) (rationalEmbed right)
    embedSubtract : ∀ left right →
      rationalEmbed (left - right)
      ≡ Spine._-_ R (rationalEmbed left) (rationalEmbed right)
    embedMultiply : ∀ left right →
      rationalEmbed (left * right)
      ≡ Spine._*_ R (rationalEmbed left) (rationalEmbed right)
    embedOrder : ∀ {left right} →
      left ≤ right → Spine._≤_ R (rationalEmbed left) (rationalEmbed right)
    embedStrictOrder : ∀ {left right} →
      left < right → Spine._<_ R (rationalEmbed left) (rationalEmbed right)

    valueBelowAbsolute : ∀ value →
      Spine._≤_ R value (Spine.abs R value)
    negativeAbsoluteBelowValue : ∀ value →
      Spine._≤_ R (Spine.neg R (Spine.abs R value)) value
    absoluteNonnegative : ∀ value →
      Spine._≤_ R (Spine.zero R) (Spine.abs R value)
    squareReflectsOrderOnNonnegative : ∀ {left right} →
      Spine._≤_ R (Spine.zero R) left →
      Spine._≤_ R (Spine.zero R) right →
      Spine._≤_ R
        (Spine._*_ R left left)
        (Spine._*_ R right right) →
      Spine._≤_ R left right

    ltTransitive : ∀ {a b c} →
      Spine._<_ R a b → Spine._<_ R b c → Spine._<_ R a c
    ltToLe : ∀ {a b} → Spine._<_ R a b → Spine._≤_ R a b
    addStrictMonotone : ∀ {a b c d} →
      Spine._<_ R a b → Spine._<_ R c d →
      Spine._<_ R (Spine._+_ R a c) (Spine._+_ R b d)
    subtractSameRightStrict : ∀ {a b} →
      Spine._<_ R a b → ∀ right →
      Spine._<_ R
        (Spine._-_ R a right)
        (Spine._-_ R b right)

open ConstructiveRealSpineOrderedFieldCapability public

asEnvelopeCapability : ∀ R →
  ConstructiveRealSpineOrderedFieldCapability R →
  Adapter.ConstructiveRealSpineEnvelopeCapability R
asEnvelopeCapability R field = record
  { rationalEmbed = rationalEmbed field
  ; leqReflexive = leqReflexive field
  ; leqTransitive = leqTransitive field
  ; addMonotone = addMonotone field
  ; multiplyMonotoneNonnegative = multiplyMonotoneNonnegative field
  ; negateAntitone = negateAntitone field
  ; negateAdd = negateAdd field
  ; embedZero = embedZero field
  ; embedOne = embedOne field
  ; embedAdd = embedAdd field
  ; embedMultiply = embedMultiply field
  ; embedOrder = embedOrder field
  }

asAbsoluteOrderCapability : ∀ R
    (field : ConstructiveRealSpineOrderedFieldCapability R) →
  Derived.ConstructiveRealSpineAbsoluteOrderCapability
    R (asEnvelopeCapability R field)
asAbsoluteOrderCapability R field = record
  { valueBelowAbsolute = valueBelowAbsolute field
  ; negativeAbsoluteBelowValue = negativeAbsoluteBelowValue field
  }

asSquareOrderCapability : ∀ R
    (field : ConstructiveRealSpineOrderedFieldCapability R) →
  SquaredClosure.ConstructiveRealSpineSquareOrderCapability
    R
    (asEnvelopeCapability R field)
    (asAbsoluteOrderCapability R field)
asSquareOrderCapability R field = record
  { absoluteNonnegative = absoluteNonnegative field
  ; squareReflectsOrderOnNonnegative =
      squareReflectsOrderOnNonnegative field
  }

asStrictOrderedSubtractionCapability : ∀ R →
  ConstructiveRealSpineOrderedFieldCapability R →
  Interval.StrictOrderedSubtractionCapability R
asStrictOrderedSubtractionCapability R field = record
  { ltTransitive = ltTransitive field
  ; ltToLe = ltToLe field
  ; addStrictMonotone = addStrictMonotone field
  ; subtractSameRightStrict = subtractSameRightStrict field
  }

nativeOrderedFieldCapabilitiesUnified : Bool
nativeOrderedFieldCapabilitiesUnified = true

nativeRationalEmbeddingSupportsStrictIntervalArithmetic : Bool
nativeRationalEmbeddingSupportsStrictIntervalArithmetic = true

concreteNativeOrderedFieldCapabilityClosed : Bool
concreteNativeOrderedFieldCapabilityClosed = false

nativeOrderedFieldCapabilitiesUnifiedIsTrue :
  nativeOrderedFieldCapabilitiesUnified ≡ true
nativeOrderedFieldCapabilitiesUnifiedIsTrue = refl

nativeRationalEmbeddingSupportsStrictIntervalArithmeticIsTrue :
  nativeRationalEmbeddingSupportsStrictIntervalArithmetic ≡ true
nativeRationalEmbeddingSupportsStrictIntervalArithmeticIsTrue = refl

concreteNativeOrderedFieldCapabilityClosedIsFalse :
  concreteNativeOrderedFieldCapabilityClosed ≡ false
concreteNativeOrderedFieldCapabilityClosedIsFalse = refl
