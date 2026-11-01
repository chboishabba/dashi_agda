module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound18Validation where

-- Focused validation root for the literal local analytic/Hessian/propagator
-- continuation.  It extends round seventeen with:
--
--   * actual Bishop sine/cosine squared-chord control;
--   * endpoint-safe literal quaternion exponential and sinc cancellation;
--   * four-dimensional Lagrange, Cauchy--Schwarz and chord-triangle algebra
--       from one explicit Bishop square-root backend;
--   * concrete noncommutative Duhamel telescoping and finite simple integrals;
--   * literal CMP109 path derivative support, including orientation-sensitive
--       positive/negative periodic bond occurrences;
--   * literal Wilson + gauge + constraint second variation;
--   * promotion through the five configured Hessian channels to 1/32;
--   * the explicit side-four residual R=I-HG* and numerical calibration
--       N=3072, r0=8, s=2, M=21, epsilon=2^-21;
--   * promotion of the collar-21 entry estimate to a weighted half contraction;
--   * coupled physical RG macrostep conclusions;
--   * exact dyadic physical clustering exponent transport;
--   * explicit 1/64 continuum plaquette noncollapse calibration.
--
-- The root does not turn the remaining square-root construction, physical
-- entry/atom/RG/clustering/cutoff estimates or Bochner completion into axioms.
-- Their proof levels remain conditional.

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound17Validation
import DASHI.Physics.YangMills.BalabanP33BishopQuaternionExponentialSquaredChordExact
import DASHI.Physics.YangMills.BalabanP33BishopLiteralQuaternionExponentialChordExact
import DASHI.Physics.YangMills.BalabanP33BishopR4ChordMetricFromSquareRootExact
import DASHI.Physics.YangMills.BalabanP33QuaternionDuhamelIntegrandTelescopeExact
import DASHI.Physics.YangMills.BalabanP33FiniteQuaternionSimpleDuhamelIntegralExact
import DASHI.Physics.YangMills.BalabanP33CMP109LiteralPathDerivativeKernelExact
import DASHI.Physics.YangMills.BalabanP33CMP109PeriodicContourEdgeKernelExact
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact
import DASHI.Physics.YangMills.BalabanP33LiteralHessianFiveChannelPromotionExact
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact
import DASHI.Physics.YangMills.BalabanP33PhysicalResidualHalfContractionAtCollar21Exact
import DASHI.Physics.YangMills.BalabanClayPhysicalCoupledMacrostepPromotionExact
import DASHI.Physics.YangMills.BalabanClayDyadicPhysicalClusteringExponentExact
import DASHI.Physics.YangMills.BalabanClayPlaquetteNoncollapseContinuumCalibrationExact
