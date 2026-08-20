module DASHI.Environment.LESResearchCrossPollinationRound6Exact where

------------------------------------------------------------------------
-- ROUND 6: AMBIGUITY, TEMPORAL ORDER AND STRUCTURED RESIDUALS
--
-- The cross-project analyses expose three remaining pieces that should be core
-- mathematics rather than project-local prose:
--
--   1. P/Q/R hypothesis semantics: dormant/reopenable is not refuted;
--   2. interval events: ordering is proof-relevant and `before` composes;
--   3. structured residuals: equal global scalar burden need not preserve a
--      consumer-local residual coordinate.
--
-- The theorem owners live in DASHI.Core; this LES module only welds them into
-- the environmental research surface so later LES runtimes cannot regress to
-- Boolean inactivity, prose-only timing, or one undifferentiated residual.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Data.Empty using (⊥)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Kernel
import DASHI.Core.ReopenableHypothesisForestExact as Hypothesis
import DASHI.Core.StructuredResidualProductExact as Residual
import DASHI.Core.TypedIntervalEventTransitionExact as Temporal

------------------------------------------------------------------------
-- Exact P/Q/R law exported for LES source/model/scenario alternatives.
------------------------------------------------------------------------

lesDormantAlternativeCannotBecomeRefutedWithoutReevaluation :
  ∀ {H}
    {semantics : Hypothesis.HypothesisSemantics H}
    {hypothesis : H}
    {reason : Hypothesis.DormancyReason} →
  Hypothesis.HypothesisTransition semantics hypothesis
    (Hypothesis.reopenable reason) Hypothesis.refuted →
  ⊥
lesDormantAlternativeCannotBecomeRefutedWithoutReevaluation =
  Hypothesis.noDirectDormantRefutation

------------------------------------------------------------------------
-- Equal summed residual does not suffice for a local consumer.  This is the
-- exact two-coordinate obstruction behind keeping conservation, calibration,
-- scenario and other residual axes separate until the declared consumer has a
-- proved aggregation/descent theorem.
------------------------------------------------------------------------

lesGlobalResidualScalarisationDefect :
  Kernel.ConsumerDescentDefect Residual.scalarTotal Residual.firstCoordinate
lesGlobalResidualScalarisationDefect = Residual.scalarTotalLosesFirstCoordinate

------------------------------------------------------------------------
-- Temporal ordering theorem is reused directly by seasonal/event planning.
------------------------------------------------------------------------

lesBeforeEventsCompose :
  ∀ {first middle last} →
  Temporal.Before first middle →
  Temporal.Before middle last →
  Temporal.Before first last
lesBeforeEventsCompose = Temporal.beforeTransitive

record LESRound6Boundary : Set where
  constructor lesRound6Boundary
  field
    dormantAlternativesRemainDistinctFromRefutations : Bool
    temporalOrderUsesProofBearingIntervals : Bool
    structuredResidualsPrecedeConsumerScalarisation : Bool
    domainScoresAndPhysicalLawsRemainExternal : Bool

canonicalLESRound6Boundary : LESRound6Boundary
canonicalLESRound6Boundary =
  lesRound6Boundary true true true true
