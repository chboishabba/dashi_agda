module DASHI.Foundations.BishopConstructiveRealBridgeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (proj₂)

import Real as BishopReal
import RealProperties as BishopProperties
import Inverse as BishopInverse
import Sequence as BishopSequence

import DASHI.Foundations.RealAnalysisAxioms as DASHIReal
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Constructive-real provenance and scope.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- BSc Honours thesis, Dalhousie University, April 2022.
-- arXiv:2205.08354.  No DOI was assigned to the thesis.
-- Supervisor: Peter Selinger.
--
-- Code lineage: viktorcsimma/bishop, pinned by vendor/bishop.  The repository
-- continues Murray's implementation of Bishop reals.  Its Real.agda defines
-- regular rational sequences, arithmetic and constructive order; Sequence.agda
-- proves Cauchy completeness, uniqueness of limits, algebraic limit laws and
-- absolute-convergence transfer.
--
-- This module is a literal adapter to those checked definitions.  It does not
-- identify Bishop's setoid equality with Agda propositional equality, and it
-- does not claim that the library already defines sine, cosine, exp or log.
------------------------------------------------------------------------

Bishopℝ : Set
Bishopℝ = BishopReal.ℝ

bishopZero bishopOne : Bishopℝ
bishopZero = BishopReal.0ℝ
bishopOne = BishopReal.1ℝ

bishopAdd bishopSub bishopMul : Bishopℝ → Bishopℝ → Bishopℝ
bishopAdd = BishopReal._+_
bishopSub = BishopReal._-_
bishopMul = BishopReal._*_

bishopNeg bishopAbs : Bishopℝ → Bishopℝ
bishopNeg = BishopReal.-_
bishopAbs = BishopReal.∣_∣

BishopEquivalent BishopLessEqual BishopStrictLess : Bishopℝ → Bishopℝ → Set
BishopEquivalent = BishopReal._≃_
BishopLessEqual = BishopReal._≤_
BishopStrictLess = BishopReal._<_

BishopConvergesTo : (Nat → Bishopℝ) → Bishopℝ → Set
BishopConvergesTo = BishopSequence._ConvergesTo_

BishopConvergent BishopCauchy : (Nat → Bishopℝ) → Set
BishopConvergent = BishopSequence._isConvergent
BishopCauchy = BishopSequence._isCauchy

BishopSeriesConvergent : (Nat → Bishopℝ) → Set
BishopSeriesConvergent terms =
  BishopConvergent (BishopSequence.SeriesOf terms)

BishopAbsoluteSeriesConvergent : (Nat → Bishopℝ) → Set
BishopAbsoluteSeriesConvergent =
  BishopSequence.SeriesOf_ConvergesAbsolutely

bishopConvergentImpliesCauchy :
  ∀ {sequence : Nat → Bishopℝ} →
  BishopConvergent sequence →
  BishopCauchy sequence
bishopConvergentImpliesCauchy = BishopSequence.fast-convergent⇒cauchy

bishopCauchyComplete :
  ∀ {sequence : Nat → Bishopℝ} →
  BishopCauchy sequence →
  BishopConvergent sequence
bishopCauchyComplete = BishopSequence.fast-cauchy⇒convergent

bishopLimitUnique :
  ∀ {sequence : Nat → Bishopℝ} {left right : Bishopℝ} →
  BishopConvergesTo sequence left →
  BishopConvergesTo sequence right →
  BishopEquivalent left right
bishopLimitUnique = BishopSequence.uniqueness-of-limits

bishopAbsoluteSeriesConverges :
  ∀ {terms : Nat → Bishopℝ} →
  BishopAbsoluteSeriesConvergent terms →
  BishopSeriesConvergent terms
bishopAbsoluteSeriesConverges = BishopSequence.absolute⇒isConvergent

bishopSeriesLimit :
  (terms : Nat → Bishopℝ) →
  BishopAbsoluteSeriesConvergent terms →
  Bishopℝ
bishopSeriesLimit terms absolute =
  BishopSequence.lim (bishopAbsoluteSeriesConverges absolute)

bishopSeriesLimitConvergence :
  (terms : Nat → Bishopℝ) →
  (absolute : BishopAbsoluteSeriesConvergent terms) →
  BishopConvergesTo
    (BishopSequence.SeriesOf terms)
    (bishopSeriesLimit terms absolute)
bishopSeriesLimitConvergence terms absolute =
  proj₂ (bishopAbsoluteSeriesConverges absolute)

bishopSeriesLimitUnique :
  (terms : Nat → Bishopℝ) →
  (absolute : BishopAbsoluteSeriesConvergent terms) →
  ∀ {other : Bishopℝ} →
  BishopConvergesTo (BishopSequence.SeriesOf terms) other →
  BishopEquivalent (bishopSeriesLimit terms absolute) other
bishopSeriesLimitUnique terms absolute otherConvergence =
  bishopLimitUnique
    (bishopSeriesLimitConvergence terms absolute)
    otherConvergence

------------------------------------------------------------------------
-- Transport into DASHI's pre-existing postulated real socket.
--
-- The submodule removes the need to postulate a second completeness theorem.
-- A remaining choice is architectural: either migrate analytic consumers to
-- Bishopℝ directly, or provide this explicit structure-preserving transport.
-- The transport is intentionally a record, not a hidden equality of carriers.
------------------------------------------------------------------------

record BishopToDASHIRealBridge : Set₁ where
  field
    embed : Bishopℝ → DASHIReal.ℝ

    embedZero : embed bishopZero ≡ DASHIReal.0ℝ
    embedOne : embed bishopOne ≡ DASHIReal.1ℝ

    embedAdd : ∀ left right →
      embed (bishopAdd left right)
      ≡ DASHIReal._+ℝ_ (embed left) (embed right)

    embedSub : ∀ left right →
      embed (bishopSub left right)
      ≡ DASHIReal._-ℝ_ (embed left) (embed right)

    embedMul : ∀ left right →
      embed (bishopMul left right)
      ≡ DASHIReal._*ℝ_ (embed left) (embed right)

    embedNeg : ∀ value →
      embed (bishopNeg value) ≡ DASHIReal.-ℝ_ (embed value)

    embedAbs : ∀ value →
      embed (bishopAbs value) ≡ DASHIReal.absℝ (embed value)

    embedEquivalent : ∀ {left right} →
      BishopEquivalent left right → embed left ≡ embed right

    embedLessEqual : ∀ {left right} →
      BishopLessEqual left right →
      DASHIReal._≤ℝ_ (embed left) (embed right)

    embedStrictLess : ∀ {left right} →
      BishopStrictLess left right →
      DASHIReal._<ℝ_ (embed left) (embed right)

    DASHIConvergesTo :
      (Nat → DASHIReal.ℝ) → DASHIReal.ℝ → Set

    convergencePreserved :
      ∀ {sequence limit} →
      BishopConvergesTo sequence limit →
      DASHIConvergesTo
        (λ index → embed (sequence index))
        (embed limit)

open BishopToDASHIRealBridge public

bishopConcreteRealCarrierLevel : ProofLevel
bishopConcreteRealCarrierLevel = machineChecked

bishopCauchyCompletenessLevel : ProofLevel
bishopCauchyCompletenessLevel = machineChecked

bishopAbsoluteSeriesTransferLevel : ProofLevel
bishopAbsoluteSeriesTransferLevel = machineChecked

bishopToDASHITransportInputsLevel : ProofLevel
bishopToDASHITransportInputsLevel = conditional
