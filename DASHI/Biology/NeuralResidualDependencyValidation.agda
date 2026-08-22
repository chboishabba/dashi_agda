module DASHI.Biology.NeuralResidualDependencyValidation where

------------------------------------------------------------------------
-- Focused cumulative root for residual-dependency cross-pollination.
--
-- Checks together:
--   * coarse neural observation non-descent;
--   * separating local dependency probes;
--   * reach-preserving residual decoupling; and
--   * future-language capability preservation.
------------------------------------------------------------------------

open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.NeuralResidualDependencyBridgeExact
import DASHI.Biology.NeuralResidualFutureLanguageBridgeExact

neuralResidualDependencyRoot : Set
neuralResidualDependencyRoot = ⊤

neuralResidualDependencyRootInhabited : neuralResidualDependencyRoot
neuralResidualDependencyRootInhabited = tt
