{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityP1SemanticSourceFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.ExoticGravity.AntigravityP1A2CertifiedStressCylinderExact as CertifiedA2
import DASHI.Physics.ExoticGravity.AntigravityP1A2OpenLemmaASTExact as A2AST
import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004QExact as Q1
import DASHI.Physics.Foundations.CMP119CosmologyA2LocalCWilsonPresentationCompilerExact as A2
import DASHI.Physics.Foundations.CMP119CosmologyR109PairObservableUnderdeterminationExact as Under

------------------------------------------------------------------------
-- CURRENT-MASTER P1 SOURCE FRONTIER
--
-- Current master has already eliminated the presentation-level E24 debt:
--
--   * the selected observable is the canonical Local-C encoded stress;
--   * the published Wilson application supplies positive-time admissibility;
--   * the same application supplies gauge invariance.
--
-- What it deliberately does NOT supply is an eliminator from the opaque
-- Round109 source-native ordinary/characteristic pair to that configuration
-- observable.  `R109PairObservableUnderdeterminationExact` proves that the bare
-- pair cannot determine a unique evaluator.
--
-- This branch makes that trust boundary executable twice, at complementary
-- levels:
--
--   * `AntigravityP1A2CertifiedStressCylinderExact` gives the consumer-facing
--     compiler once source semantics are supplied;
--   * `AntigravityP1A2OpenLemmaASTExact` gives the exact typed syntax/goal split
--     for the still-open source lemma, so constructing the AST cannot count as
--     constructing its proof.
--
-- Therefore the antigravity-specific P1 frontier still has exactly TWO source
-- leaves:
--
--   Q1  actual present-cut source-path derivative semantics + B4 equivariance;
--   A2  the selected Round109 pair denotes the canonical Local-C stress
--       cylinder observable.
--
-- No new positivity, clustering, observable-choice, or covariance estimate is
-- independently scheduled.
------------------------------------------------------------------------

selectedObservableChoiceStillRequired : Bool
selectedObservableChoiceStillRequired = false

positiveTimeAdmissibilityStillRequired : Bool
positiveTimeAdmissibilityStillRequired = false

gaugeInvariantAdmissibilityStillRequired : Bool
gaugeInvariantAdmissibilityStillRequired = false

pairToCanonicalLocalCObservableSemanticsStillRequired : Bool
pairToCanonicalLocalCObservableSemanticsStillRequired =
  A2.remainingA2SourceDebtIsPairToObservableSameObjectSemantics

-- The physical A2 equality is still open, but once supplied it now compiles to
-- the functional/Wilson presentation without any additional E2/E4 proof leaf.
a2SameObjectReceiptCompilesCertifiedWilsonPresentation : Bool
a2SameObjectReceiptCompilesCertifiedWilsonPresentation =
  CertifiedA2.observableChoiceCompilerOwned

a2OpenLemmaASTDefined : Bool
a2OpenLemmaASTDefined = true

a2ASTConstructionPaysSourceSemantics : Bool
a2ASTConstructionPaysSourceSemantics = false

a2SourceSemanticPackageCount : Nat
a2SourceSemanticPackageCount = A2AST.a2SourceSemanticPackageCount

a2InternalOpenInvariantCount : Nat
a2InternalOpenInvariantCount = A2AST.a2InternalOpenInvariantCount

a2NonSelectedPairImagesConstrained : Bool
a2NonSelectedPairImagesConstrained = A2AST.nonSelectedPairImagesConstrainedByA2

a2EvaluatorInjectivityRequired : Bool
a2EvaluatorInjectivityRequired = A2AST.evaluatorInjectivityRequired

a2EvaluatorSurjectivityRequired : Bool
a2EvaluatorSurjectivityRequired = A2AST.evaluatorSurjectivityRequired

a2AllPairSemanticsRequired : Bool
a2AllPairSemanticsRequired = A2AST.allPairSemanticsRequired

q1PathDerivativeSourcePackageStillRequired : Bool
q1PathDerivativeSourcePackageStillRequired =
  Q1.q1IsPathDerivativeSemanticsAndEquivariance

bareR109PairContainsObservableEvaluator : Bool
bareR109PairContainsObservableEvaluator =
  Under.r109PairCarrierContainsSelectedObservableEvaluator

remainingP1SourceLeafCount : Nat
remainingP1SourceLeafCount = 2

remainingOpaqueAnalyticEstimateCount : Nat
remainingOpaqueAnalyticEstimateCount = 0

remainingP1WorkIsSourceSemantics : Bool
remainingP1WorkIsSourceSemantics = true

selectedObservableChoiceStillRequiredIsFalse :
  selectedObservableChoiceStillRequired ≡ false
selectedObservableChoiceStillRequiredIsFalse = refl

positiveTimeAdmissibilityStillRequiredIsFalse :
  positiveTimeAdmissibilityStillRequired ≡ false
positiveTimeAdmissibilityStillRequiredIsFalse = refl

gaugeInvariantAdmissibilityStillRequiredIsFalse :
  gaugeInvariantAdmissibilityStillRequired ≡ false
gaugeInvariantAdmissibilityStillRequiredIsFalse = refl

pairToCanonicalLocalCObservableSemanticsStillRequiredIsTrue :
  pairToCanonicalLocalCObservableSemanticsStillRequired ≡ true
pairToCanonicalLocalCObservableSemanticsStillRequiredIsTrue = refl

q1PathDerivativeSourcePackageStillRequiredIsTrue :
  q1PathDerivativeSourcePackageStillRequired ≡ true
q1PathDerivativeSourcePackageStillRequiredIsTrue = refl

bareR109PairContainsObservableEvaluatorIsFalse :
  bareR109PairContainsObservableEvaluator ≡ false
bareR109PairContainsObservableEvaluatorIsFalse = refl

a2ASTConstructionPaysSourceSemanticsIsFalse :
  a2ASTConstructionPaysSourceSemantics ≡ false
a2ASTConstructionPaysSourceSemanticsIsFalse = refl

remainingP1WorkIsSourceSemanticsIsTrue :
  remainingP1WorkIsSourceSemantics ≡ true
remainingP1WorkIsSourceSemanticsIsTrue = refl
