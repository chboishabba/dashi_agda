{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004LExact where

------------------------------------------------------------------------
-- SOURCE-CALCULATION FRONTIER / OVERLAY L / 2026-10-04.
--
-- Overlay K proves the preferred route is compiler-saturated with four source
-- evidence payments.  This overlay does not add a fifth payment.  It sharpens
-- the literal source calculations that instantiate A2 and B2:
--
-- A2  The arbitrary insertion-meaning predicate is gone.  The exact selected
--     source payment is one Configuration -> R cylinder observable together
--     with the published Wilson positive-time and gauge-admissibility proofs.
--     No evaluator for every R109 pair is required.
--
-- B2  Once the selected Eq. (2.23) source bounds factor through the same
--     positive finite partition/density integral Z,
--
--       N_ERB <= M_ERB * Z,
--       N_V    = c_V * Z,
--
--     the coefficient-level inequality
--
--       M_ERB + Tail_109(k) < - c_V
--
--     already implies
--
--       Tail_109(k) * Z < D_Weyl Z.
--
--     Thus no separate numerical bound/evaluation of Z is a source leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004KExact as K
import DASHI.Physics.Foundations.CMP119CosmologyR109LiteralStressCylinderMaxCutExact as A2Literal
import DASHI.Physics.Foundations.CMP119CosmologyR109WilsonAdmissibleStressCylinderExact as A2Wilson
import DASHI.Physics.Foundations.CMP119CosmologyPartitionTailSourceScalarMarginExact as B2Scalar
import DASHI.Physics.Foundations.CMP119CosmologyPartitionDerivativeTailMarginExact as B2Terminal

data PreferredSourceEvidenceResidual : Set where
  a1-literal-source-local-geometry-and-derivative-naturality :
    PreferredSourceEvidenceResidual
  a2-selected-wilson-admissible-r109-cylinder :
    PreferredSourceEvidenceResidual
  b1-selected-cutoff-direct-r136-r144-r109-tail-anchor :
    PreferredSourceEvidenceResidual
  b2-eq223-coefficient-margin-beats-r109-tail :
    PreferredSourceEvidenceResidual

preferredSourceEvidenceResidualCount : Nat
preferredSourceEvidenceResidualCount = 4

remainingCompilerDebtCount : Nat
remainingCompilerDebtCount = 0

------------------------------------------------------------------------
-- A1/B1 remain exactly Overlay K's source payments.
------------------------------------------------------------------------

a1PreferredProducerIsSourceNaturalityAndGeometry : Bool
a1PreferredProducerIsSourceNaturalityAndGeometry =
  K.a1PreferredProducerIsSourceNaturalityAndGeometry

b1DirectTailAnchorRemainsSourceEvidence : Bool
b1DirectTailAnchorRemainsSourceEvidence =
  K.b1DirectTailAnchorRemainsSourceEvidence

------------------------------------------------------------------------
-- A2 least-privilege source presentation.
------------------------------------------------------------------------

a2ArbitraryMeaningPredicateEliminated : Bool
a2ArbitraryMeaningPredicateEliminated =
  A2Literal.arbitraryStressInsertionMeaningPredicateEliminated

a2PublishedOSPredicatesPinned : Bool
a2PublishedOSPredicatesPinned =
  A2Wilson.publishedOSAdmissibilityPredicatesArePinned

a2RequiresGlobalPairEvaluator : Bool
a2RequiresGlobalPairEvaluator = false

a2RemainingSourceDataAreSelectedObservableAndPublishedAdmissibility : Bool
a2RemainingSourceDataAreSelectedObservableAndPublishedAdmissibility =
  A2Wilson.remainingE2E4PhysicalProofsArePublishedPositiveTimeAndGaugeAdmissibility

------------------------------------------------------------------------
-- B2 normalization-free coefficient source margin.
------------------------------------------------------------------------

b2PartitionNormalizationValueNotNeeded : Bool
b2PartitionNormalizationValueNotNeeded =
  B2Scalar.partitionNormalizationValueNotNeededForCoefficientMargin

b2CoefficientMarginPaysPartitionTailDominance : Bool
b2CoefficientMarginPaysPartitionTailDominance =
  B2Scalar.preferredB2CanBePaidByERBPlusTailBelowNegativeVacuumCoefficient

b2TerminalObjectRemainsOnePointPartitionResponse : Bool
b2TerminalObjectRemainsOnePointPartitionResponse =
  B2Terminal.sourceFacingB2IsOnePointPartitionResponse

b2NeedsIndependentPartitionUpperBound : Bool
b2NeedsIndependentPartitionUpperBound = false

------------------------------------------------------------------------
-- Final accounting.
------------------------------------------------------------------------

preferredRouteCompilerSaturated : Bool
preferredRouteCompilerSaturated = K.preferredRouteCompilerSaturated

preferredRouteRemainingLeavesAreAllSourceEvidence : Bool
preferredRouteRemainingLeavesAreAllSourceEvidence =
  K.preferredRouteRemainingLeavesAreAllSourceEvidence

preferredRouteRemainingAdapterConstructionCount : Nat
preferredRouteRemainingAdapterConstructionCount = 0
