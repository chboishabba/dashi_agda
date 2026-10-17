{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261008AAExact where

------------------------------------------------------------------------
-- OVERLAY AA / 2026-10-08: FINAL PACKAGE COMPRESSION AFTER YM C1
-- CROSS-POLLINATION.
--
-- The terminal preferred package schedule is:
--
--   S1  active regular-E/localization source witness;
--   S3a one selected physical-F^2 marked-source package;
--   S2  selected-F2 / Hilbert-trace same-object application to renormalized
--       trace-anomaly authority;
--   S3b weighted product-Haar Eq.(1.71) partition + oscillation package.
--
-- S1 is now additionally frozen by an exact typed AST.  At each actual active
-- scale it has exactly four unproved source coordinates: E_k, component family,
-- localized activities, and the exact localized-composite-sum equality.  The
-- active-scale witness is an index, not a fifth invariant.  No inactive-scale
-- extension, quantitative Section-2 package, Background equality, or ten tangent
-- choices are hidden inside the S1 package.
--
-- This is package compression only.  No conditional physical theorem is
-- promoted to machineChecked.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261008ZExact as Z
import DASHI.Physics.Foundations.CMP119CosmologyS1LiteralActiveRegularEASTExact as S1AST
import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedF2HilbertMaxCutExact as F2Hilbert
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact as Curvature

remainingPreferredPackageCount : Nat
remainingPreferredPackageCount = 4

remainingAdapterDebt : Nat
remainingAdapterDebt = 0

------------------------------------------------------------------------
-- S1: one source lemma, exactly four internal unproved invariants.
------------------------------------------------------------------------

s1LiteralActiveRegularEFormWitnessRequired : Bool
s1LiteralActiveRegularEFormWitnessRequired =
  Z.s1LiteralActiveRegularEFormWitnessRequired

s1FullTheorem1QuantitativePackageRequired : Bool
s1FullTheorem1QuantitativePackageRequired =
  Z.s1FullTheorem1QuantitativePackageRequired

s1UnprovenInvariantCount : Nat
s1UnprovenInvariantCount = S1AST.unprovenInvariantCount

s1InactiveScaleExtensionRequired : Bool
s1InactiveScaleExtensionRequired = S1AST.requiresInactiveScaleExtension

s1PostHocBackgroundEqualityRequired : Bool
s1PostHocBackgroundEqualityRequired = S1AST.requiresPostHocBackgroundEquality

s1IndependentTenTangentChoicesRequired : Bool
s1IndependentTenTangentChoicesRequired =
  S1AST.requiresIndependentTenTangentChoices

s1ASTCompilesToExistingRound246Witness : Bool
s1ASTCompilesToExistingRound246Witness =
  S1AST.astCompilesToActiveRegularESection2FormWitness

------------------------------------------------------------------------
-- S3a is ONE selected physical-F2 package.
------------------------------------------------------------------------

s3aOneSelectedPhysicalF2PackageRequired : Bool
s3aOneSelectedPhysicalF2PackageRequired = true

s3aPostHocR129MarkedSourceEqualityRequired : Bool
s3aPostHocR129MarkedSourceEqualityRequired = false

s3aPostHocLocalCF2OperatorEqualityRequired : Bool
s3aPostHocLocalCF2OperatorEqualityRequired = false

s3aCoefficientEnergyIndependentProjectRequired : Bool
s3aCoefficientEnergyIndependentProjectRequired = false

s3aGaugeLocalIndependentProjectRequired : Bool
s3aGaugeLocalIndependentProjectRequired = false

s3aInternalUniformCoefficientEnergyStillRequired : Bool
s3aInternalUniformCoefficientEnergyStillRequired =
  F2Hilbert.remainingSelectedF2HilbertSourceWorkIsUniformCoefficientEnergy

s3aInternalCoefficientSameObjectIdentificationStillRequired : Bool
s3aInternalCoefficientSameObjectIdentificationStillRequired =
  F2Hilbert.remainingSelectedF2CoefficientSameObjectIdentificationRequired

s3aPackageIncludesGaugeLocalSemantics : Bool
s3aPackageIncludesGaugeLocalSemantics = true

s3aNuclearCompletionCompilerOwned : Bool
s3aNuclearCompletionCompilerOwned = true

------------------------------------------------------------------------
-- S2 unchanged except it consumes the selected S3a object directly.
------------------------------------------------------------------------

s2IndependentLocalCF2ScalarIdentificationRequired : Bool
s2IndependentLocalCF2ScalarIdentificationRequired =
  Z.s2IndependentLocalCF2ScalarIdentificationRequired

s2FreshRenormalizedTraceAnomalyIdentityRequired : Bool
s2FreshRenormalizedTraceAnomalyIdentityRequired =
  Z.s2FreshRenormalizedTraceAnomalyIdentityRequired

s2SelectedF2ToRenormalizedF2SameObjectRequired : Bool
s2SelectedF2ToRenormalizedF2SameObjectRequired =
  Z.s2SelectedF2ToRenormalizedF2SameObjectRequired

s2LocalHilbertTraceToRenormalizedTraceSameObjectRequired : Bool
s2LocalHilbertTraceToRenormalizedTraceSameObjectRequired =
  Z.s2LocalHilbertTraceToRenormalizedTraceSameObjectRequired

------------------------------------------------------------------------
-- S3b unchanged at its canonical weighted-Haar floor.
------------------------------------------------------------------------

s3bWeightedTaggedPartitionFamilyRequired : Bool
s3bWeightedTaggedPartitionFamilyRequired =
  Z.s3bWeightedTaggedPartitionFamilyRequired

s3bWeightedOscillationVanishesRequired : Bool
s3bWeightedOscillationVanishesRequired =
  Z.s3bWeightedOscillationVanishesRequired

s3bSingleSliceExactQuadratureShortcutRequired : Bool
s3bSingleSliceExactQuadratureShortcutRequired = false

s3bIndependentMassDiscrepancyRequired : Bool
s3bIndependentMassDiscrepancyRequired = false

------------------------------------------------------------------------
-- Final stopping rule.
------------------------------------------------------------------------

remainingWorkIsFourPhysicalSourcePackages : Bool
remainingWorkIsFourPhysicalSourcePackages = true

representationOnlySameObjectDebtRemains : Bool
representationOnlySameObjectDebtRemains = false

noConditionalSourceLeafPromoted : Bool
noConditionalSourceLeafPromoted = true

fullFriedmannTrajectoryAlreadySolved : Bool
fullFriedmannTrajectoryAlreadySolved = false
