module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound35PlaquetteCurlValidation where

------------------------------------------------------------------------
-- Cumulative Round Thirty Five validation root.
--
-- Imports Round Thirty Four, then adds the next proof-bearing Gate-I tranche:
--
--   * the literal first derivative of the physical ordered plaquette is the
--     sum of exactly four oriented Leibniz terms;
--   * its physical right-trivialization is exactly
--
--       Ad_A X0 + Ad_AB X1 - Ad_AB X2 - Ad_ABC^-1 X3;
--
--   * the transport order is derived from the actual positive/inverse jets;
--   * the covariant-minus-flat curl is exactly the signed sum of four adjoint
--     defects, each factorized through explicit link-minus-identity terms;
--   * the theorem is instantiated on the same selected variational background
--     and perturbation object used by terminal coercivity;
--   * an exact rational adversarial test proves that the configured radius and
--     flat cancellation alone do not imply the target correlated curvature
--     scale.
--
-- The selected-background Euler--Lagrange curvature estimate and grouped
-- sixteen-atom nonlinear lower bound remain open.  No W-local witness is
-- fabricated from the radius stress test.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound34PhysicalRadiusWLocalValidation
import DASHI.Physics.YangMills.BalabanP33PhysicalPlaquetteFirstVariationExact
import DASHI.Physics.YangMills.BalabanP33PhysicalCovariantPlaquetteCurlExact
import DASHI.Physics.YangMills.BalabanP33CovariantCurlDefectFactorizationExact
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCovariantCurlInstantiationExact
import DASHI.Physics.YangMills.BalabanP33FlatPlaquetteFirstVariationCurlExact
import DASHI.Physics.YangMills.BalabanP33CovariantCurlRadiusStressTestExact
