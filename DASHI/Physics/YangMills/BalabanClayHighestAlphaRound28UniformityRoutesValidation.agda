module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound28UniformityRoutesValidation where

------------------------------------------------------------------------
-- Cumulative validation root.
--
-- Imports Round Twenty Seven and checks:
--
--   * the reflection-positive observable route is distinct from the
--     coercive-Hessian/Combes--Thomas/Schur route;
--   * the observable projection is concretely non-injective with respect to
--     the spectral tag;
--   * exact two-point moment curvature is a nonnegative square;
--   * the RG good class is a dependent state carrying all uniform caps;
--   * a supplied one-step producer constructs the next good scale; and
--   * two exact remainder contractions compose to theta squared.
--
-- No selected-background radius, W-local producer, literal Hessian inverse,
-- reflection-positive-to-spectral bridge, physical RG good-class producer,
-- thermodynamic gap, OS reconstruction or Clay completion is asserted.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound27Validation
import DASHI.Physics.Common.GradedLocalCompatibilitySystemExact
import DASHI.Physics.YangMills.BalabanP33ReflectionPositivityHessianBoundaryExact
import DASHI.Physics.YangMills.BalabanP33TwoPointMomentCurvatureExact
import DASHI.Physics.YangMills.BalabanP33RGGoodClassPreservationExact
