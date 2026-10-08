{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261008ZExact where

------------------------------------------------------------------------
-- OVERLAY Z / 2026-10-08: SOURCE-FIRST R129 F2 + DIRECT ANOMALY WELD +
-- CANONICAL WEIGHTED EQ.(1.71) HAAR REFINEMENT.
--
-- This overlay removes the remaining presentation-level duplications exposed
-- after Y:
--
-- S1  Round247's active regular-E/localization form witness is the sole source
--     payment; the CMP109/116 continuation on PublishedB is compiler output.
--
-- S3a R129 already exports the exact SameFamilyMarkedSourceData.  Select that
--     source by construction; no post-hoc R129 marked-source equality remains.
--     Physical F2 meaning, uniform source normalization/radii, and gauge/local
--     semantics remain genuine source work.
--
-- S2  consume the selected completed F2 directly in the imported renormalized
--     trace/F2 authority.  No second arbitrary Local-C F2 scalar remains.
--
-- S3b use the canonical Haar-weighted refinement-indexed Gate4 route.  Exact
--     cell masses kill discrepancy by construction; the one-shot exact-slice
--     shortcut is not a premise.  Remaining source/analysis is the literal
--     weighted tagged partition family plus a vanishing cell-oscillation
--     modulus (for which Lipschitz+shrinking-mesh remains an available producer).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261008YExact as Y
import DASHI.Physics.Foundations.CMP119CosmologyP1ActiveRegularEToPublishedBExact as S1
import DASHI.Physics.Foundations.CMP119CosmologyP3R129SelectedF2ByConstructionExact as S3a
import DASHI.Physics.Foundations.CMP119CosmologyP2SelectedF2TraceAuthorityExact as S2
import DASHI.Physics.Foundations.CMP119CosmologyP3LipschitzOscillationCompilerExact as Lipschitz
import DASHI.Physics.YangMills.BalabanCMP122Equation171WeightedGate4RefinementLimitExact as Weighted

remainingModelSpecificSourcePackageCount : Nat
remainingModelSpecificSourcePackageCount = 4

remainingStandardImportedAuthorityCount : Nat
remainingStandardImportedAuthorityCount = Y.remainingStandardImportedAuthorityCount

remainingPreferredPackageCount : Nat
remainingPreferredPackageCount = 4

remainingAdapterDebt : Nat
remainingAdapterDebt = 0

------------------------------------------------------------------------
-- S1: literal active regular-E/localization source witness only.
------------------------------------------------------------------------

s1PublishedBContinuationCompilerClosed : Bool
s1PublishedBContinuationCompilerClosed =
  S1.activeRegularEFormToPublishedBContinuationCompilerClosed

s1FullTheorem1QuantitativePackageRequired : Bool
s1FullTheorem1QuantitativePackageRequired =
  S1.fullTheorem1QuantitativePackageRequiredForS1

s1LiteralActiveRegularEFormWitnessRequired : Bool
s1LiteralActiveRegularEFormWitnessRequired =
  S1.literalActiveRegularEFormOnPublishedBStillRequired

s1PostHocBackgroundEqualityRequired : Bool
s1PostHocBackgroundEqualityRequired = false

s1TenIndependentTangentEqualitiesRequired : Bool
s1TenIndependentTangentEqualitiesRequired = false

------------------------------------------------------------------------
-- S3a: choose the R129 selected source definitionally.
------------------------------------------------------------------------

s3aPostHocR129MarkedSourceEqualityRequired : Bool
s3aPostHocR129MarkedSourceEqualityRequired =
  S3a.postHocR129MarkedSourceEqualityRequired

s3aPostHocLocalCF2OperatorEqualityRequired : Bool
s3aPostHocLocalCF2OperatorEqualityRequired =
  S3a.postHocLocalCF2OperatorEqualityRequired

s3aSelectedPhysicalF2SemanticsRequired : Bool
s3aSelectedPhysicalF2SemanticsRequired =
  S3a.remainingS3aWorkIsSelectedPhysicalF2Semantics

s3aUniformCoefficientRadiusAndNormalizationRequired : Bool
s3aUniformCoefficientRadiusAndNormalizationRequired = true

s3aGaugeLocalSemanticsRequired : Bool
s3aGaugeLocalSemanticsRequired = true

------------------------------------------------------------------------
-- S2: selected F2 -> imported renormalized operator pair.
------------------------------------------------------------------------

s2IndependentLocalCF2ScalarIdentificationRequired : Bool
s2IndependentLocalCF2ScalarIdentificationRequired =
  S2.independentLocalCF2ScalarIdentificationRequired

s2FreshRenormalizedTraceAnomalyIdentityRequired : Bool
s2FreshRenormalizedTraceAnomalyIdentityRequired =
  S2.freshRenormalizedTraceAnomalyIdentityRequired

s2SelectedF2ToRenormalizedF2SameObjectRequired : Bool
s2SelectedF2ToRenormalizedF2SameObjectRequired =
  S2.selectedF2ToRenormalizedF2SameObjectRequired

s2LocalHilbertTraceToRenormalizedTraceSameObjectRequired : Bool
s2LocalHilbertTraceToRenormalizedTraceSameObjectRequired =
  S2.localHilbertTraceToRenormalizedTraceSameObjectRequired

------------------------------------------------------------------------
-- S3b: canonical weighted product-Haar refinement.
------------------------------------------------------------------------

s3bSingleSliceExactQuadratureShortcutRequired : Bool
s3bSingleSliceExactQuadratureShortcutRequired = false

s3bIndependentMassDiscrepancyRequired : Bool
s3bIndependentMassDiscrepancyRequired = false

s3bWeightedTaggedPartitionFamilyRequired : Bool
s3bWeightedTaggedPartitionFamilyRequired = true

s3bWeightedOscillationVanishesRequired : Bool
s3bWeightedOscillationVanishesRequired = true

s3bSeparateGenericFiniteRealizationPackageRequired : Bool
s3bSeparateGenericFiniteRealizationPackageRequired = false

s3bLipschitzMeshIsAvailableOscillationProducer : Bool
s3bLipschitzMeshIsAvailableOscillationProducer = true

s3bIndependentOscillationLimitAfterLipschitzMeshRequired : Bool
s3bIndependentOscillationLimitAfterLipschitzMeshRequired =
  Lipschitz.independentOscillationVanishingTheoremRequired

------------------------------------------------------------------------
-- Global stopping rule.
------------------------------------------------------------------------

remainingWorkIsPhysicalSourceMathematics : Bool
remainingWorkIsPhysicalSourceMathematics = true

sameObjectWorkOnlyAtPhysicalSourceSemantics : Bool
sameObjectWorkOnlyAtPhysicalSourceSemantics = true

representationOnlySameObjectDebtRemains : Bool
representationOnlySameObjectDebtRemains = false

fullFriedmannTrajectoryAlreadySolved : Bool
fullFriedmannTrajectoryAlreadySolved = false

noSyntheticPhysicalIdentificationAdded : Bool
noSyntheticPhysicalIdentificationAdded = true
