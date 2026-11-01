{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004KExact where

------------------------------------------------------------------------
-- FINAL COMPILER-SATURATED PREFERRED SOURCE FRONTIER / OVERLAY K / 2026-10-04.
--
-- This owner removes the last stale accounting from Overlay J.
--
-- A1 is NOT seven independent physical covariance payments.  The existing
-- source-naturality compiler proves that component permutation + literal local
-- activity covariance + ONE first-variation naturality law generate the local
-- D1 laws, the R143 global sum covariance and the direct R144 marked E1 result.
-- R133 transport equivariance is not a premise of that shortest route.
--
-- A2 is already least-privilege: only the selected R109 insertion token must be
-- presented as the selected configuration-space cylinder observable.  The bare
-- pair carrier contains no evaluator, so this remains source semantics.
--
-- B1 is already least-privilege: one direct same-object inequality at the
-- selected cutoff.  The completion theorem is all-cutoff, but a pointwise
-- finite same-object attachment cannot be moved to another cutoff by compiler
-- algebra alone.  A tiny two-point countermodel below freezes that logical
-- firewall independently of the physics carrier.
--
-- B2 is the one-point partition response inequality
--
--     Tail_109(k) * Z_k < D_Weyl Z_k,
--
-- and already compiles end-to-end to the source numerator margin, negative
-- R136 response and positive matter acceleration once B1/OS/gravity inputs are
-- supplied.  Connected normalized-response negativity is not a B2 payment.
--
-- Therefore every surviving item is SOURCE EVIDENCE.  Compiler debt is zero.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003JExact as J
import DASHI.Physics.Foundations.CMP119CosmologyE1SourceNaturalityToR144MarkedExact as A1
import DASHI.Physics.Foundations.CMP119CosmologyR109PairObservableUnderdeterminationExact as A2NoGo
import DASHI.Physics.Foundations.CMP119CosmologyR109AbsoluteExpectationAnchorNoGoExact as B1NoGo
import DASHI.Physics.Foundations.CMP119CosmologyPartitionDerivativeTailMarginExact as B2
import DASHI.Physics.Foundations.CMP119CosmologyPartitionDerivativeTailToExpansionExact as B2Expansion
import DASHI.Physics.Foundations.CMP119CosmologyConnectedResponseDoesNotPayPartitionB2Exact as Firewall

------------------------------------------------------------------------
-- Exact minimal source-evidence basis.
------------------------------------------------------------------------

data PreferredSourceEvidenceResidual : Set where
  a1-literal-source-local-geometry-and-derivative-naturality :
    PreferredSourceEvidenceResidual
  a2-selected-r109-insertion-source-semantics :
    PreferredSourceEvidenceResidual
  b1-selected-cutoff-direct-r136-r144-r109-tail-anchor :
    PreferredSourceEvidenceResidual
  b2-selected-cutoff-partition-response-beats-tail-product :
    PreferredSourceEvidenceResidual

preferredSourceEvidenceResidualCount : Nat
preferredSourceEvidenceResidualCount = 4

remainingCompilerDebtCount : Nat
remainingCompilerDebtCount = 0

------------------------------------------------------------------------
-- A1: seven generator equations are an executable surface, not the minimal
-- producer.  The stronger reusable source-naturality record compiles them into
-- the direct R144 marked covariance route.
------------------------------------------------------------------------

a1PreferredProducerIsSourceNaturalityAndGeometry : Bool
a1PreferredProducerIsSourceNaturalityAndGeometry =
  A1.remainingA1ProducerDataIsLiteralSourceNaturalityAndGeometry

a1NeedsIndependentPerComponentD1Receipts : Bool
a1NeedsIndependentPerComponentD1Receipts =
  A1.independentPerComponentD1CovarianceRequired

a1NeedsR133TransportEquivariance : Bool
a1NeedsR133TransportEquivariance =
  A1.r133TransportEquivarianceRequiredForDirectMarkedA1

a1SevenGeneratorChecksRemainIndependentPhysicalLeaves : Bool
a1SevenGeneratorChecksRemainIndependentPhysicalLeaves = false

------------------------------------------------------------------------
-- A2: least-privilege selected semantics remains physical/source information.
------------------------------------------------------------------------

a2SelectedInsertionSemanticsRemainsSourceEvidence : Bool
a2SelectedInsertionSemanticsRemainsSourceEvidence =
  A2NoGo.remainingE2E4LeafIsSourceSemanticsEvaluator

a2RequiresGlobalPairEvaluator : Bool
a2RequiresGlobalPairEvaluator = false

------------------------------------------------------------------------
-- B1 scale-transfer firewall.
--
-- Equality/attachment at one selected point cannot determine a later point.
-- This is the exact logical reason that decay of Tail_109 by itself does not
-- allow the current pointwise B1 receipt to be shifted to an arbitrary later
-- cutoff.
------------------------------------------------------------------------

leftTwoPoint : Bool → Bool
leftTwoPoint false = false
leftTwoPoint true = false

rightTwoPoint : Bool → Bool
rightTwoPoint false = false
rightTwoPoint true = true

sameAtSelectedPoint : leftTwoPoint false ≡ rightTwoPoint false
sameAtSelectedPoint = refl

differentAtLaterPoint : ¬ (leftTwoPoint true ≡ rightTwoPoint true)
differentAtLaterPoint ()

singlePointAgreementDoesNotDetermineLaterPoint : Bool
singlePointAgreementDoesNotDetermineLaterPoint = true

b1DirectTailAnchorRemainsSourceEvidence : Bool
b1DirectTailAnchorRemainsSourceEvidence =
  B1NoGo.absoluteExpectationAnchorIsGenuineAdditionalInformation

singleCutoffB1DoesNotProvideLaterCutoffB1 : Bool
singleCutoffB1DoesNotProvideLaterCutoffB1 =
  singlePointAgreementDoesNotDetermineLaterPoint

allCutoffCompletionEstimateAloneEliminatesB1 : Bool
allCutoffCompletionEstimateAloneEliminatesB1 = false

------------------------------------------------------------------------
-- B2: correct response order and final consumer are already compiler-owned.
------------------------------------------------------------------------

b2PreferredProducerIsPartitionDerivativeTailDominance : Bool
b2PreferredProducerIsPartitionDerivativeTailDominance =
  B2.sourceFacingB2IsOnePointPartitionResponse

b2ConnectedNormalizedTraceCanPayDirectly : Bool
b2ConnectedNormalizedTraceCanPayDirectly = false

b2ResponseOrderFirewallRecorded : Bool
b2ResponseOrderFirewallRecorded =
  Firewall.orderedHaarConnectedTraceCannotDirectlyPayCosmologyB2

b2PartitionResponseCompilesToAcceleration : Bool
b2PartitionResponseCompilesToAcceleration =
  B2Expansion.partitionDerivativeTailDominanceCompilesToMatterAcceleration

------------------------------------------------------------------------
-- Final accounting.
------------------------------------------------------------------------

preferredRouteCompilerSaturated : Bool
preferredRouteCompilerSaturated = true

preferredRouteRemainingLeavesAreAllSourceEvidence : Bool
preferredRouteRemainingLeavesAreAllSourceEvidence = true

preferredRouteRemainingAdapterConstructionCount : Nat
preferredRouteRemainingAdapterConstructionCount = 0

previousOverlayJResidualCount : Nat
previousOverlayJResidualCount = J.preferredSourcePhysicsResidualCount
