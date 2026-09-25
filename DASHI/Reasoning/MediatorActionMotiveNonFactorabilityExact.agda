module DASHI.Reasoning.MediatorActionMotiveNonFactorabilityExact where

------------------------------------------------------------------------
-- COMPATIBILITY OWNER
--
-- Same mediation action can arise from distinct motives.  The constructive
-- collision theorem is owned by TrialecticMemoryLearningHyperfabricExact;
-- this module preserves the earlier requested naming surface.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.TrialecticMemoryLearningHyperfabricExact as Trialectic

mediationMotiveDoesNotFactorThroughAction =
  Trialectic.mediationMotiveDoesNotFactorThroughAction

didMediateDoesFactorThroughObservedAction =
  Trialectic.didMediateFactorsThroughObservedAction
