module DASHI.Foundations.LegacyDASHIRealEquivalenceAuthorityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Foundations.RealAnalysisAxioms as Legacy
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Explicit foundational commitment relating the legacy DASHI real socket to
-- Bishop's concrete constructive reals.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- BSc Honours thesis, Dalhousie University, April 2022.
-- arXiv:2205.08354.  No DOI was assigned.
--
-- This file does not assert an inhabitant.  It specifies the one layered
-- authority that would be sufficient, and from which downstream transports are
-- derived.  Repeated ad-hoc bridge axioms are therefore unnecessary.
------------------------------------------------------------------------

record LegacyRealMathematicalEquality : Set₁ where
  infix 12 _≈D_
  field
    _≈D_ : Legacy.ℝ → Legacy.ℝ → Set
    ≈D-refl : ∀ {x} → x ≈D x
    ≈D-sym : ∀ {x y} → x ≈D y → y ≈D x
    ≈D-trans : ∀ {x y z} → x ≈D y → y ≈D z → x ≈D z
    propositionalEqualitySound : ∀ {x y} → x ≡ y → x ≈D y

open LegacyRealMathematicalEquality public

record BishopDASHIOrderedFieldEquivalence
    (equality : LegacyRealMathematicalEquality) : Set₁ where
  infix 12 _≈D_
  _≈D_ = LegacyRealMathematicalEquality._≈D_ equality
  field
    toDASHI : Bishop.Bishopℝ → Legacy.ℝ
    toBishop : Legacy.ℝ → Bishop.Bishopℝ

    bishopRoundTrip : ∀ x →
      Bishop.BishopEquivalent (toBishop (toDASHI x)) x
    dashiRoundTrip : ∀ x → toDASHI (toBishop x) ≈D x

    bishopEqualityPreserved : ∀ {x y} →
      Bishop.BishopEquivalent x y → toDASHI x ≈D toDASHI y
    bishopEqualityReflected : ∀ {x y} →
      toDASHI x ≈D toDASHI y → Bishop.BishopEquivalent x y

    preservesZero : toDASHI Bishop.bishopZero ≈D Legacy.0ℝ
    preservesOne : toDASHI Bishop.bishopOne ≈D Legacy.1ℝ
    preservesAdd : ∀ x y →
      toDASHI (Bishop.bishopAdd x y)
      ≈D Legacy._+ℝ_ (toDASHI x) (toDASHI y)
    preservesSub : ∀ x y →
      toDASHI (Bishop.bishopSub x y)
      ≈D Legacy._-ℝ_ (toDASHI x) (toDASHI y)
    preservesMul : ∀ x y →
      toDASHI (Bishop.bishopMul x y)
      ≈D Legacy._*ℝ_ (toDASHI x) (toDASHI y)
    preservesNeg : ∀ x →
      toDASHI (Bishop.bishopNeg x) ≈D Legacy.-ℝ_ (toDASHI x)
    preservesAbs : ∀ x →
      toDASHI (Bishop.bishopAbs x) ≈D Legacy.absℝ (toDASHI x)

    preservesLe : ∀ {x y} →
      Bishop.BishopLessEqual x y → Legacy._≤ℝ_ (toDASHI x) (toDASHI y)
    reflectsLe : ∀ {x y} →
      Legacy._≤ℝ_ (toDASHI x) (toDASHI y) → Bishop.BishopLessEqual x y
    preservesLt : ∀ {x y} →
      Bishop.BishopStrictLess x y → Legacy._<ℝ_ (toDASHI x) (toDASHI y)
    reflectsLt : ∀ {x y} →
      Legacy._<ℝ_ (toDASHI x) (toDASHI y) → Bishop.BishopStrictLess x y

    rationalEmbeddingAgreement : Set
    inverseAndApartnessAgreement : Set
    absoluteMetricAgreement : Set

open BishopDASHIOrderedFieldEquivalence public

record BishopDASHICompleteRealEquivalence
    {equality : LegacyRealMathematicalEquality}
    (fieldEquivalence : BishopDASHIOrderedFieldEquivalence equality) : Set₁ where
  field
    LegacySequence : Set
    legacySequenceAt : LegacySequence → Nat → Legacy.ℝ
    LegacyCauchy : LegacySequence → Set
    LegacyConvergesTo : LegacySequence → Legacy.ℝ → Set

    bishopSequenceToLegacy : (Nat → Bishop.Bishopℝ) → LegacySequence
    legacySequenceToBishop : LegacySequence → Nat → Bishop.Bishopℝ

    preservesConvergence : ∀ {sequence limit} →
      Bishop.BishopConvergesTo sequence limit →
      LegacyConvergesTo
        (bishopSequenceToLegacy sequence)
        (toDASHI fieldEquivalence limit)

    reflectsConvergence : ∀ {sequence limit} →
      LegacyConvergesTo
        (bishopSequenceToLegacy sequence)
        (toDASHI fieldEquivalence limit) →
      Bishop.BishopConvergesTo sequence limit

    preservesCauchy : ∀ {sequence} →
      Bishop.BishopCauchy sequence → LegacyCauchy (bishopSequenceToLegacy sequence)

    reflectsCauchy : ∀ {sequence} →
      LegacyCauchy sequence → Bishop.BishopCauchy (legacySequenceToBishop sequence)

    preservesSeriesSums : Set
    reflectsSeriesSums : Set
    completenessTransported : Set

open BishopDASHICompleteRealEquivalence public

record BishopDASHIElementaryFunctionEquivalence
    {equality : LegacyRealMathematicalEquality}
    {fieldEquivalence : BishopDASHIOrderedFieldEquivalence equality}
    (completeEquivalence : BishopDASHICompleteRealEquivalence fieldEquivalence) : Set₁ where
  infix 12 _≈D_
  _≈D_ = LegacyRealMathematicalEquality._≈D_ equality
  field
    bishopSin bishopCos bishopExp : Bishop.Bishopℝ → Bishop.Bishopℝ
    dashiSin dashiCos dashiExp : Legacy.ℝ → Legacy.ℝ

    bishopPositive : Bishop.Bishopℝ → Set
    dashiPositive : Legacy.ℝ → Set
    bishopLog : (x : Bishop.Bishopℝ) → bishopPositive x → Bishop.Bishopℝ
    dashiLog : (x : Legacy.ℝ) → dashiPositive x → Legacy.ℝ

    sinAgreement : ∀ x →
      toDASHI fieldEquivalence (bishopSin x)
      ≈D dashiSin (toDASHI fieldEquivalence x)
    cosAgreement : ∀ x →
      toDASHI fieldEquivalence (bishopCos x)
      ≈D dashiCos (toDASHI fieldEquivalence x)
    expAgreement : ∀ x →
      toDASHI fieldEquivalence (bishopExp x)
      ≈D dashiExp (toDASHI fieldEquivalence x)

    positivityPreserved : ∀ {x} → bishopPositive x →
      dashiPositive (toDASHI fieldEquivalence x)
    logAgreement : ∀ x positive →
      toDASHI fieldEquivalence (bishopLog x positive)
      ≈D dashiLog
        (toDASHI fieldEquivalence x)
        (positivityPreserved positive)

open BishopDASHIElementaryFunctionEquivalence public

record LegacyRealEquivalenceAuthority : Set₁ where
  field
    equality : LegacyRealMathematicalEquality
    orderedField : BishopDASHIOrderedFieldEquivalence equality
    completeReal : BishopDASHICompleteRealEquivalence orderedField
    elementaryFunctions : BishopDASHIElementaryFunctionEquivalence completeReal

open LegacyRealEquivalenceAuthority public

legacyEquivalenceArchitectureLevel : ProofLevel
legacyEquivalenceArchitectureLevel = machineChecked

legacyEquivalenceExistenceLevel : ProofLevel
legacyEquivalenceExistenceLevel = conditional
