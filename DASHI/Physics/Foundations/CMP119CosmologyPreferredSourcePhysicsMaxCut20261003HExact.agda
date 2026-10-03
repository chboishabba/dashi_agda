{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003HExact where

------------------------------------------------------------------------
-- FINAL SOURCE-NATIVE PREFERRED MAX-CUT / OVERLAY H / 2026-10-03.
--
-- After eliminating receipt adapters, arbitrary finite endpoint sequences and
-- the over-strong E/R/B/vacuum decomposition at the terminal sign interface,
-- the preferred route has exactly FOUR model-specific source payments:
--
-- A1  the selected rational R144 finite-D1 readout obeys the canonical signed
--     B4 covariance law on the physical whole-lattice family;
--
-- A2  the literal selected R109 stress insertion denotes the one selected
--     configuration-space cylinder observable (whose Wilson positive-time and
--     gauge admissibility are already pinned to that same image);
--
-- B1  one direct same-object tail inequality
--       embed(Q_R136) <= embed(DGamma_k) + embed(Tail_109(k));
--
-- B2  one literal source-native unnormalized inequality
--       N_k + Tail_109(k) * Z_k < 0.
--
-- B2 is strictly closer to the literal finite source than the older sufficient
-- condition c_V < -(M_ERB + Tail).  Positive Z converts this one numerator
-- margin into DGamma_k + Tail < 0, and B1 then gives Q_R136 < 0.  The direct
-- source-numerator terminal owner now feeds that exact sign into the existing
-- marked-OS / Local-C matter-acceleration consumer.  The older Eq.(2.23)
-- E/R/B/vacuum envelope remains a producer strategy, not the final terminal
-- source interface.
--
-- The four residuals below are intentionally NOT inhabited here.  Existing
-- finite countermodels/no-go owners prove that the currently weaker repository
-- data do not determine them.  This file therefore completes the max-cut
-- without manufacturing missing source physics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyE1LinearityDoesNotForceB4CovarianceExact as A1NoGo
import DASHI.Physics.Foundations.CMP119CosmologyR109PairObservableUnderdeterminationExact as A2NoGo
import DASHI.Physics.Foundations.CMP119CosmologyR109AbsoluteExpectationAnchorNoGoExact as B1NoGo
import DASHI.Physics.Foundations.CMP119CosmologyR144R109DirectTailAnchorExact as B1
import DASHI.Physics.Foundations.CMP119CosmologyDirectTailFromSourceNumeratorExact as B2
import DASHI.Physics.Foundations.CMP119CosmologyUnnormalizedSourceTailMarginExact as NumeratorMargin
import DASHI.Physics.Foundations.CMP119CosmologyDirectSourceNumeratorTailToExpansionExact as DirectTerminal
import DASHI.Physics.Foundations.CMP119CosmologyEq223ERBMetricVariationUnderdeterminationExact as ERBNoGo
import DASHI.Physics.Foundations.CMP119CosmologyEq223VacuumMetricSignUnderdeterminationExact as VacuumNoGo
import DASHI.Physics.Foundations.CMP119CosmologyPreferredA1CanonicalReceiptAdapterExact as A1Adapter
import DASHI.Physics.Foundations.CMP119CosmologyPreferredA2SelectedReceiptAdapterExact as A2Adapter

data PreferredSourcePhysicsResidual : Set where
  a1-selected-r144-rational-signed-b4-covariance :
    PreferredSourcePhysicsResidual

  a2-selected-r109-insertion-source-semantics :
    PreferredSourcePhysicsResidual

  b1-direct-r136-r144-r109-tail-anchor :
    PreferredSourcePhysicsResidual

  b2-literal-source-numerator-tail-margin :
    PreferredSourcePhysicsResidual

preferredSourcePhysicsResidualCount : Nat
preferredSourcePhysicsResidualCount = 4

------------------------------------------------------------------------
-- A1: no adapter debt; one genuine source/change-of-variables theorem.
------------------------------------------------------------------------

a1CannotBeDerivedFromAdditiveLinearityAlone : Bool
a1CannotBeDerivedFromAdditiveLinearityAlone =
  A1NoGo.sourceNaturalityOrDirectCovarianceStillRequired

a1TypedReceiptIsCompilerOutputOnceCovarianceExists : Bool
a1TypedReceiptIsCompilerOutputOnceCovarianceExists =
  A1Adapter.a1CanonicalCovarianceToTypedReceiptIsCompilerOnly

------------------------------------------------------------------------
-- A2: no global evaluator is needed, but the bare pair token cannot determine
-- its configuration-space meaning by itself.
------------------------------------------------------------------------

a2BareR109PairDoesNotDetermineSelectedObservable : Bool
a2BareR109PairDoesNotDetermineSelectedObservable =
  A2NoGo.remainingE2E4LeafIsSourceSemanticsEvaluator

a2TypedReceiptIsCompilerOutputOnceSelectedPresentationExists : Bool
a2TypedReceiptIsCompilerOutputOnceSelectedPresentationExists =
  A2Adapter.a2SelectedPresentationToTypedReceiptIsCompilerOnly

------------------------------------------------------------------------
-- B1: one direct same-object inequality.  Difference/Cauchy information alone
-- cannot fix the missing absolute additive constant.
------------------------------------------------------------------------

b1IsOneDirectSameObjectTailInequality : Bool
b1IsOneDirectSameObjectTailInequality =
  B1.preferredB1CompressedToOneDirectTailInequality

b1CannotBeRecoveredFromR109DifferenceDataAlone : Bool
b1CannotBeRecoveredFromR109DifferenceDataAlone =
  B1NoGo.absoluteExpectationAnchorIsGenuineAdditionalInformation

b1ConsumerNeedsFiniteFamilyOrObservable : Bool
b1ConsumerNeedsFiniteFamilyOrObservable =
  B1.consumerNeedsFiniteFamilyOrObservable

------------------------------------------------------------------------
-- B2: final source-facing sign condition.
------------------------------------------------------------------------

b2IsOneUnnormalizedSourceNumeratorTailMargin : Bool
b2IsOneUnnormalizedSourceNumeratorTailMargin =
  B2.remainingSourceSignPaymentCanBeOneNumeratorTailMargin

b2RequiresERBVacuumDecomposition : Bool
b2RequiresERBVacuumDecomposition =
  B2.eq223ERBVacuumDecompositionIsRequiredTerminalB2Interface

b2NumeratorMarginCompilesToNormalizedPreferredMargin : Bool
b2NumeratorMarginCompilesToNormalizedPreferredMargin =
  NumeratorMargin.sourceNumeratorMarginIsSufficientForPreferredB2

b1b2DirectSourceMarginCompilesToMatterAcceleration : Bool
b1b2DirectSourceMarginCompilesToMatterAcceleration =
  DirectTerminal.directSourceNumeratorTailMarginCompilesToMatterAcceleration

rawEq223ObjectsAloneDoNotFixRequiredMetricSign : Bool
rawEq223ObjectsAloneDoNotFixRequiredMetricSign =
  andBool
    ERBNoGo.sourceBackedERBMetricVariationStillRequired
    VacuumNoGo.sourceBackedVacuumMetricVariationStillRequired
  where
    andBool : Bool → Bool → Bool
    andBool true right = right
    andBool false _ = false

------------------------------------------------------------------------
-- Final accounting.
------------------------------------------------------------------------

remainingAdapterConstructionCount : Nat
remainingAdapterConstructionCount = 0

allFourSourceEvidencePaymentsDerivedInternally : Bool
allFourSourceEvidencePaymentsDerivedInternally = false

olderEq223VacuumThresholdRemainsSufficientProducerButNotMinCut : Bool
olderEq223VacuumThresholdRemainsSufficientProducerButNotMinCut = true

preferredSourceMaxCutIsNowEvidenceOnly : Bool
preferredSourceMaxCutIsNowEvidenceOnly = true
