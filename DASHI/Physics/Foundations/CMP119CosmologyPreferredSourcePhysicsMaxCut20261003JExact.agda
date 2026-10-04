{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003JExact where

------------------------------------------------------------------------
-- CORRECTED FINAL SOURCE MAX-CUT / OVERLAY J / 2026-10-03.
--
-- This combines the two valid reductions that survive the response-order audit:
--
-- A1  canonical signed R144 covariance is reduced to the seven literal
--     hypercubic generator checks.
--
-- B2  the terminal source-facing sign is the ONE-POINT partition response
--
--       Tail_109(k) * Z_k < D_Weyl Z_k,
--
--     not the connected derivative of a normalized insertion.  A correct
--     quantitative split is therefore
--
--       Tail_109(k) * Z_k <= budget < D_Weyl Z_k.
--
-- A2 and B1 remain same-object source payments.  No adapter is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003IExact as I
import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003I1Exact as I1
import DASHI.Physics.Foundations.CMP119CosmologyPartitionDerivativeTailMarginExact as PartitionB2
import DASHI.Physics.Foundations.CMP119CosmologyConnectedResponseDoesNotPayPartitionB2Exact as Firewall
import DASHI.Physics.Foundations.CMP119CosmologyR109PairObservableUnderdeterminationExact as A2NoGo
import DASHI.Physics.Foundations.CMP119CosmologyR109AbsoluteExpectationAnchorNoGoExact as B1NoGo

data PreferredSourcePhysicsResidual : Set where
  a1-seven-literal-hypercubic-generator-covariances :
    PreferredSourcePhysicsResidual
  a2-selected-r109-insertion-source-semantics :
    PreferredSourcePhysicsResidual
  b1-direct-r136-r144-r109-tail-anchor :
    PreferredSourcePhysicsResidual
  b2-partition-derivative-beats-r109-tail-product :
    PreferredSourcePhysicsResidual

preferredSourcePhysicsResidualCount : Nat
preferredSourcePhysicsResidualCount = 4

------------------------------------------------------------------------
-- A1: finite generator surface.
------------------------------------------------------------------------

a1LiteralGeneratorCheckCount : Nat
a1LiteralGeneratorCheckCount = I.a1LiteralGeneratorCheckCount

a1CanonicalB4CovarianceReducesToSevenGeneratorChecks : Bool
a1CanonicalB4CovarianceReducesToSevenGeneratorChecks =
  I.a1CanonicalB4CovarianceReducesToSevenGeneratorChecks

------------------------------------------------------------------------
-- B2: correct response-order budget compiler.
------------------------------------------------------------------------

partitionTailBudgetForcesDominance :
  ∀ {tailTimesPartition budget partitionDerivative : ℚ} →
  tailTimesPartition ≤ budget →
  budget < partitionDerivative →
  tailTimesPartition < partitionDerivative
partitionTailBudgetForcesDominance tailBelowBudget budgetBelowResponse =
  ℚP.≤-<-trans tailBelowBudget budgetBelowResponse

record PartitionResponseTailBudgetCertificate
    (tailTimesPartition partitionDerivative : ℚ) : Set where
  field
    budget : ℚ
    tailProductBelowBudget : tailTimesPartition ≤ budget
    budgetBelowPartitionDerivative : budget < partitionDerivative

open PartitionResponseTailBudgetCertificate public

partitionResponseTailBudgetCertificateForcesDominance :
  ∀ {tailTimesPartition partitionDerivative} →
  PartitionResponseTailBudgetCertificate
    tailTimesPartition partitionDerivative →
  tailTimesPartition < partitionDerivative
partitionResponseTailBudgetCertificateForcesDominance certificate =
  partitionTailBudgetForcesDominance
    (tailProductBelowBudget certificate)
    (budgetBelowPartitionDerivative certificate)

b2TerminalLeafIsPartitionDerivativeTailDominance : Bool
b2TerminalLeafIsPartitionDerivativeTailDominance =
  PartitionB2.partitionDerivativeTailDominanceIsSufficientForB2

b2PartitionResponseHasTwoBoundCompiler : Bool
b2PartitionResponseHasTwoBoundCompiler = true

b2SourceFacingObjectIsOnePointResponse : Bool
b2SourceFacingObjectIsOnePointResponse =
  PartitionB2.sourceFacingB2IsOnePointPartitionResponse

connectedOrderedHaarTracePaysB2Directly : Bool
connectedOrderedHaarTracePaysB2Directly = false

connectedVsPartitionFirewallRecorded : Bool
connectedVsPartitionFirewallRecorded =
  Firewall.orderedHaarConnectedTraceCannotDirectlyPayCosmologyB2

------------------------------------------------------------------------
-- A2 / B1 remain source same-object information.
------------------------------------------------------------------------

a2RemainsOneSelectedSemanticsLeaf : Bool
a2RemainsOneSelectedSemanticsLeaf =
  A2NoGo.remainingE2E4LeafIsSourceSemanticsEvaluator

b1RemainsOneAbsoluteDirectTailLeaf : Bool
b1RemainsOneAbsoluteDirectTailLeaf =
  B1NoGo.absoluteExpectationAnchorIsGenuineAdditionalInformation

------------------------------------------------------------------------
-- Final accounting.
------------------------------------------------------------------------

remainingAdapterConstructionCount : Nat
remainingAdapterConstructionCount = 0

previousNumeratorBudgetIsNotCanonicalTerminalB2Interface : Bool
previousNumeratorBudgetIsNotCanonicalTerminalB2Interface = true

partitionDerivativeTailDominanceIsPreferredTerminalB2 : Bool
partitionDerivativeTailDominanceIsPreferredTerminalB2 =
  I1.b2TerminalLeafIsPartitionDerivativeTailDominance

preferredSourceMaxCutIsEvidenceOnly : Bool
preferredSourceMaxCutIsEvidenceOnly = true
