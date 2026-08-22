module DASHI.Biology.NeuralResidualDependencyValidation where

------------------------------------------------------------------------
-- Focused cumulative root for residual-dependency cross-pollination.
--
-- Checks together:
--   * coarse neural observation non-descent;
--   * separating local dependency probes;
--   * reach-preserving residual decoupling;
--   * future-language capability preservation; and
--   * the exact rational 2x2 transformed-covariance seed calibrated against
--     Bansal--Jiang affine spectral-independence.
--
-- The final item is deliberately an algebraic neighbour, not a claim that the
-- neural finite model itself already carries a Bansal--Jiang covariance/SDP.
------------------------------------------------------------------------

open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.NeuralResidualDependencyBridgeExact
import DASHI.Biology.NeuralResidualFutureLanguageBridgeExact
import DASHI.Mathematics.LinearAlgebra.RationalAffineSpectralIndependence2Exact

neuralResidualDependencyRoot : Set
neuralResidualDependencyRoot = ⊤

neuralResidualDependencyRootInhabited : neuralResidualDependencyRoot
neuralResidualDependencyRootInhabited = tt
