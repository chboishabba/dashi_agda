module DASHI.Analysis.BishopConstructiveSeriesAdapterExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import RealProperties as BishopProperties
import Sequence as BishopSequence

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.BishopConstructedRealBackendExact as BishopBackend
import DASHI.Analysis.ConstructiveRealSpine as LegacySpine
import DASHI.Analysis.ConstructiveSeries as LegacySeries
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Adapter from the imported Bishop sequence/series machinery into DASHI's
-- existing ConstructiveSeries contracts.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- BSc Honours thesis, Dalhousie University, April 2022.
-- arXiv:2205.08354.  No DOI was assigned.
------------------------------------------------------------------------

bishopPartialSums : (Nat → Bishop.Bishopℝ) → Nat → Bishop.Bishopℝ
bishopPartialSums terms = BishopSequence.SeriesOf terms

record BishopConvergentSeries (terms : Nat → Bishop.Bishopℝ) : Set₁ where
  field
    absolute : Bishop.BishopAbsoluteSeriesConvergent terms

open BishopConvergentSeries public

bishopSeriesSum :
  ∀ {terms} → BishopConvergentSeries terms → Bishop.Bishopℝ
bishopSeriesSum {terms} convergent =
  Bishop.bishopSeriesLimit terms (absolute convergent)

bishopSeriesConverges :
  ∀ {terms} (convergent : BishopConvergentSeries terms) →
  Bishop.BishopConvergesTo
    (bishopPartialSums terms)
    (bishopSeriesSum convergent)
bishopSeriesConverges {terms} convergent =
  Bishop.bishopSeriesLimitConvergence terms (absolute convergent)

bishopSeriesSumUnique :
  ∀ {terms} (convergent : BishopConvergentSeries terms) {other} →
  Bishop.BishopConvergesTo (bishopPartialSums terms) other →
  Bishop.BishopEquivalent (bishopSeriesSum convergent) other
bishopSeriesSumUnique {terms} convergent =
  Bishop.bishopSeriesLimitUnique terms (absolute convergent)

------------------------------------------------------------------------
-- Quotient-aware reuse of the older ConstructiveSeries layer.
------------------------------------------------------------------------

record BishopLegacySeriesTransport
    (legacyReal : LegacySpine.ConstructedOrderedCompleteReal)
    (legacySequences : LegacySeries.FunctionSequenceRealization legacyReal) : Set₁ where
  field
    toLegacy : Bishop.Bishopℝ → LegacySpine.Real legacyReal
    termsToLegacy : (Nat → Bishop.Bishopℝ) → Nat → LegacySpine.Real legacyReal
    termsToLegacyDefinition : ∀ terms index →
      termsToLegacy terms index ≡ toLegacy (terms index)

    convergenceTransport : ∀ {terms limit} →
      Bishop.BishopConvergesTo (BishopSequence.SeriesOf terms) limit →
      LegacySpine.ConvergesTo legacyReal
        (LegacySeries.seriesPartialSums legacySequences (termsToLegacy terms))
        (toLegacy limit)

    cauchyTransport : ∀ {terms} →
      Bishop.BishopSeriesConvergent terms →
      LegacySpine.IsCauchy legacyReal
        (LegacySeries.seriesPartialSums legacySequences (termsToLegacy terms))

open BishopLegacySeriesTransport public

asLegacyConvergentSeries :
  ∀ {legacyReal legacySequences terms}
    (transport : BishopLegacySeriesTransport legacyReal legacySequences)
    (convergent : BishopConvergentSeries terms) →
  LegacySeries.ConvergentSeries
    legacyReal legacySequences (termsToLegacy transport terms)
asLegacyConvergentSeries transport convergent = record
  { partialSumsCauchy =
      cauchyTransport transport
        (Bishop.bishopAbsoluteSeriesConverges (absolute convergent))
  ; limit = toLegacy transport (bishopSeriesSum convergent)
  ; converges = convergenceTransport transport (bishopSeriesConverges convergent)
  }

record BishopComparisonRatioReuse
    (legacyReal : LegacySpine.ConstructedOrderedCompleteReal)
    (legacySequences : LegacySeries.FunctionSequenceRealization legacyReal)
    (transport : BishopLegacySeriesTransport legacyReal legacySequences) : Set₁ where
  field
    comparison : LegacySeries.ComparisonTestAuthority legacyReal legacySequences
    ratio : LegacySeries.RatioTestAuthority legacyReal legacySequences
    geometric : LegacySeries.GeometricSeriesAuthority legacyReal legacySequences

    bishopComparisonMajorantsTransport : Set
    bishopRatioCertificatesTransport : Set
    bishopGeometricTailTransport : Set

open BishopComparisonRatioReuse public

bishopSeriesLimitConstructionLevel : ProofLevel
bishopSeriesLimitConstructionLevel = machineChecked

bishopLegacySeriesTransportInputsLevel : ProofLevel
bishopLegacySeriesTransportInputsLevel = conditional

bishopComparisonRatioReuseLevel : ProofLevel
bishopComparisonRatioReuseLevel = machineChecked
