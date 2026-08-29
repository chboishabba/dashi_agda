{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound101BidiCompletionCutExact where

------------------------------------------------------------------------
-- ROUND101: FROZEN-CONSUMER BIDI CUT
--
-- This root supersedes the Round100 *preferred-route commentary* where the
-- genuine Heat/Doob log transform was tentatively identified directly with the
-- static CMP116 Hessian.  Those identity adapters remain valid as conditional
-- special cases, but are NOT the generic primary route.
--
-- BACKWARD FROM FROZEN ROW A
-- --------------------------
-- `LiteralCompactSimplePositiveBetaCompletion` requires one tuned generated
-- coupling construction plus bilateral terminal beta tails.  The actual
-- `BalabanCutoffCouplingDynamics` already contains CMP109 (5.42), identifying
-- the recurrence correction with its exact vacuum-polarisation mixed derivative.
-- Round101 proves:
--
--   pointwise betaLower <= beta_(j+1) <= betaUpper on j<K
--       -> every prefix upper ledger
--       -> every terminal-tail bilateral ledger
--       -> the frozen Row-A completion once the tuned observation window exists.
--
-- Hence neither prefix summability nor terminal-tail bilaterality is a new
-- physical theorem.  The response-kernel/quartic lane is an OPTIONAL mechanism
-- for constructing the tuning window; it is not an irreducible field of the
-- frozen endpoint.
--
-- TRUE CURRENT A SOURCE OBJECT
-- ----------------------------
-- The two-sided estimate should be proved directly on
--
--   `negativeOffDiagonalSecondMomentumDerivative`
--
-- inside the SAME `BalabanVacuumPolarisationCoefficient` carried by the actual
-- generated dynamics.  CMP109 (5.42) then transports it to betaCorrection.
-- Thus Ward/constrained-Gaussian and normalized finite-g interaction calculations
-- meet at one literal scalar rather than through a second correspondence record.
--
-- FORWARD CMP116 -> FROZEN ROW C
-- --------------------------------
-- CMP116 supplies a static differentiated marked Hessian with geometric spatial
-- decay.  A genuine Heat/Doob/log transform, however, also produces a covariance
-- of gradients.  Therefore the generic source shape is
--
--   eta_dynamic <= H_static + Cov
--
-- temporally, and
--
--   M_dynamic <= M_static + M_cov
--
-- spatially.  Round101 proves that if the covariance debt has the same 1/2 shell
-- decay / finite weighted-row control, then:
--
--   temporal eta_n <= (A_H + A_cov) (1/2)^n
--                <= (A_H + A_cov) (17/32)^n,
--
-- and the existing curvature summation closes; while spatially
--
--   weightedRow(M_dynamic) <= C_H + C_cov
--
-- and all weighted Dyson powers follow from the existing finite influence
-- compiler.  Thus the stochastic covariance estimate is isolated explicitly.
--
-- AUTHORITY
-- ---------
-- No row is promoted here.  A/B/C/D remain open and the frozen research count
-- remains four until literal same-object physical completion predicates are
-- inhabited.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound95MasterSyncExact as R100
import DASHI.Physics.YangMills.BalabanPointwiseBetaBoundsToFrozenRowAExact as APointwise
import DASHI.Physics.YangMills.BalabanVacuumPolarisationPointwiseBetaBoundsExact as AVP
import DASHI.Physics.YangMills.BalabanVacuumPolarisationTunedFamilyToFrozenRowAExact as ATuned
import DASHI.Physics.YangMills.BalabanHeatDoobHessianCovarianceDebtExact as CTemporal
import DASHI.Physics.YangMills.BalabanHeatDoobWeightedGeneratorCovarianceExact as CSpatial

------------------------------------------------------------------------
-- A: literal mixed derivative -> exact frozen additive obligations
------------------------------------------------------------------------

rowACMP109BetaIsLiteralMixedDerivativeRound101Level : ProofLevel
rowACMP109BetaIsLiteralMixedDerivativeRound101Level =
  AVP.cmp109VacuumPolarisationBetaIdentityLevel

rowALiteralDerivativeBoundsToPointwiseBetaRound101Level : ProofLevel
rowALiteralDerivativeBoundsToPointwiseBetaRound101Level =
  AVP.literalDerivativeBoundsToPointwiseBetaLevel

rowAPointwiseBoundsToPrefixRound101Level : ProofLevel
rowAPointwiseBoundsToPrefixRound101Level =
  APointwise.pointwiseBetaBoundsToPrefixLevel

rowAPointwiseBoundsToFrozenCompletionRound101Level : ProofLevel
rowAPointwiseBoundsToFrozenCompletionRound101Level =
  APointwise.pointwiseBetaBoundsToFrozenRowACompilerLevel

rowALiteralMixedDerivativeTunedFamilyToFrozenRound101Level : ProofLevel
rowALiteralMixedDerivativeTunedFamilyToFrozenRound101Level =
  ATuned.literalMixedDerivativeFamilyToFrozenRowACompilerLevel

-- Shortest physical A leaf now:
--   (A1) construct the actual generated CMP109 dynamics;
--   (A2) prove a uniform positive lower and finite upper bound on its exact
--        (5.42) mixed vacuum-polarisation derivative over the admitted history;
--   (A3) construct the tuned bare/observation window in the inverse-square
--        coordinate.  Response-kernel/quartic shooting is one route to A3.
-- Prefix and terminal-tail bounds are not separate leaves.
rowALiteralCMP109MixedDerivativeTunedFamilyRound101Level : ProofLevel
rowALiteralCMP109MixedDerivativeTunedFamilyRound101Level = conditional

------------------------------------------------------------------------
-- B -> C temporal: static CMP116 Hessian + genuine Heat/Doob covariance
------------------------------------------------------------------------

rowCHeatDoobHessianCovarianceSplitRound101Level : ProofLevel
rowCHeatDoobHessianCovarianceSplitRound101Level =
  CTemporal.heatDoobHessianCovarianceSplitCompilerLevel

rowCHeatDoobCovarianceToUniformCurvatureDebtRound101Level : ProofLevel
rowCHeatDoobCovarianceToUniformCurvatureDebtRound101Level =
  CTemporal.heatDoobCovarianceDebtToUniformCurvatureLevel

-- Physical temporal leaf:
--   * literal conditional/static Hessian response <= SAME CMP116 hessian mark;
--   * literal gradient covariance response has one cutoff/volume-uniform
--     geometric half-shell amplitude on the same Heat/Doob density.
rowCLiteralHeatDoobCovarianceSplitRound101Level : ProofLevel
rowCLiteralHeatDoobCovarianceSplitRound101Level = conditional

------------------------------------------------------------------------
-- B -> C spatial: static weighted CMP116 row + dynamic covariance response
------------------------------------------------------------------------

rowCHeatDoobWeightedGeneratorCovarianceRound101Level : ProofLevel
rowCHeatDoobWeightedGeneratorCovarianceRound101Level =
  CSpatial.heatDoobWeightedGeneratorCovarianceCompilerLevel

rowCHeatDoobWeightedGeneratorAllPowerRowsRound101Level : ProofLevel
rowCHeatDoobWeightedGeneratorAllPowerRowsRound101Level =
  CSpatial.heatDoobWeightedGeneratorAllPowerRowsLevel

-- Physical spatial leaf:
--   * static derivative-generator response is the SAME weighted CMP116 Hessian;
--   * covariance response has one finite weighted row constant on the same
--     lattice metric/density.  The complete weighted Dyson propagation is then
--     theorem-owned.
rowCLiteralHeatDoobWeightedCovarianceRound101Level : ProofLevel
rowCLiteralHeatDoobWeightedCovarianceRound101Level = conditional

------------------------------------------------------------------------
-- B remains the common source-instantiation seam
------------------------------------------------------------------------

-- One literal CMP116 differentiated marked carrier, with positive
-- cutoff/volume/scale-uniform analytic radius and correct beta/Hessian/composite/
-- stress source coordinates, still feeds both corrected C bridges above.
rowBLiteralCMP116SharedMarkedInstantiationRound101Level : ProofLevel
rowBLiteralCMP116SharedMarkedInstantiationRound101Level = conditional

------------------------------------------------------------------------
-- Frozen authority
------------------------------------------------------------------------

round101FrozenResearchCountStillFour = R100.round100FrozenResearchCountStillFour

rowACompletionRound101Level : ProofLevel
rowACompletionRound101Level = conditional

rowBCompletionRound101Level : ProofLevel
rowBCompletionRound101Level = conditional

rowCCompletionRound101Level : ProofLevel
rowCCompletionRound101Level = conditional

rowDCompletionRound101Level : ProofLevel
rowDCompletionRound101Level = conditional
