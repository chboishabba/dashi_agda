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
--   * every one of the sixteen Wilson placement defects is partitioned
--     canonically into four singleton selected-factor terms and eleven
--     higher-order terms, then summed into the literal plaquette defect;
--   * the six quadratic terms are retained in the correlated channel while
--     the four cubic terms and quartic term form the deep remainder;
--   * exact rational arithmetic proves the deep coefficient fits rho/144 but
--     the six-pair coefficient does not;
--   * square-root-free scaled Young bounds and a generic ordered quaternion
--     envelope prove the cubic--quartic lower estimate once literal physical
--     selected-factor norm envelopes are instantiated;
--   * an exact rational adversarial test proves that the configured radius and
--     flat cancellation alone do not imply the target correlated curvature
--     scale;
--   * the newly surfaced Einstein--Cartan Yang--Mills monograph and its later
--     slab-kernel paper are audited with distinct theory/operator signatures,
--     rather than treated as proof receipts.
--
-- The selected-background Euler--Lagrange curvature estimate, the physical
-- selected-factor envelope instantiation, and the sharp correlated lower bound
-- remain open.  No W-local witness is fabricated from the radius stress test.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound34PhysicalRadiusWLocalValidation
import DASHI.Physics.YangMills.BalabanP33PhysicalPlaquetteFirstVariationExact
import DASHI.Physics.YangMills.BalabanP33PhysicalCovariantPlaquetteCurlExact
import DASHI.Physics.YangMills.BalabanP33CovariantCurlDefectFactorizationExact
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCovariantCurlInstantiationExact
import DASHI.Physics.YangMills.BalabanP33FlatPlaquetteFirstVariationCurlExact
import DASHI.Physics.YangMills.BalabanP33CovariantCurlRadiusStressTestExact
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonCorrelatedDeepPartitionExact
import DASHI.Physics.YangMills.BalabanP33WilsonPairDeepBudgetExact
import DASHI.Physics.YangMills.BalabanP33QuaternionScaledYoungLowerExact
import DASHI.Physics.YangMills.BalabanP33WilsonDeepRemainderEnvelopeExact
import DASHI.Physics.YangMills.YangMillsCizekEinsteinCartanClaimAuditExact
