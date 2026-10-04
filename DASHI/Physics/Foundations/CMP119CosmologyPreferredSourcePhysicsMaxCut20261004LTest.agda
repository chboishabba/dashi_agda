{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004LTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004LExact as Subject

fourSourceEvidenceLeavesRemain :
  Subject.preferredSourceEvidenceResidualCount ≡ 4
fourSourceEvidenceLeavesRemain = refl

compilerDebtIsZero :
  Subject.remainingCompilerDebtCount ≡ 0
compilerDebtIsZero = refl

a2MeaningPredicateGone :
  Subject.a2ArbitraryMeaningPredicateEliminated ≡ true
a2MeaningPredicateGone = refl

a2UsesPublishedOSPredicates :
  Subject.a2PublishedOSPredicatesPinned ≡ true
a2UsesPublishedOSPredicates = refl

a2NoGlobalPairEvaluator :
  Subject.a2RequiresGlobalPairEvaluator ≡ false
a2NoGlobalPairEvaluator = refl

b2CancelsPartitionNormalization :
  Subject.b2PartitionNormalizationValueNotNeeded ≡ true
b2CancelsPartitionNormalization = refl

b2CoefficientMarginPaysTailDominance :
  Subject.b2CoefficientMarginPaysPartitionTailDominance ≡ true
b2CoefficientMarginPaysTailDominance = refl

b2NoIndependentPartitionUpperBound :
  Subject.b2NeedsIndependentPartitionUpperBound ≡ false
b2NoIndependentPartitionUpperBound = refl

routeStillCompilerSaturated :
  Subject.preferredRouteCompilerSaturated ≡ true
routeStillCompilerSaturated = refl
