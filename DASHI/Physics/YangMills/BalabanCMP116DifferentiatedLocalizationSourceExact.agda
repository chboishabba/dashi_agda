module DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact where

------------------------------------------------------------------------
-- ROUND84: CMP116 ANALYTIC LOCALIZATION SURVIVES SOURCE/FIELD DIFFERENTIATION
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116(1) (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- SOURCE LOCATOR
--
-- Sect. 1 begins with localized functions E(X,U,J,A) analytic in U,J,A and
-- constructs decoupled propagators/backgrounds analytic in the complex
-- parameters s(Y).  Around (1.18)--(1.21) the substituted background remains
-- analytic with bounds uniform on the declared U,J domain.  The source then
-- states explicitly:
--
--   "We differentiate it ... and represent all derivatives by the Cauchy
--    formula"
--
-- leading to (1.23).  After summing the localized terms, (1.29) retains a
-- positive exponential tree-distance factor.  Lemma 1, (1.33)--(1.36), packages
-- the resulting terms as functions localized to Y, analytic in U,J,B, with an
-- exponential bound.  The subsequent discussion applies the same construction
-- to the other fluctuation-action terms.
--
-- MATHEMATICAL CONSEQUENCE
--
-- On the source's common complex domain, taking a finite number of declared
-- field/source derivatives does not require a NEW localization theorem.  Cauchy
-- estimates cost inverse powers of the available analytic radii, while the
-- already-produced spatial/tree exponential survives.  The radii/constants must
-- of course be uniform on the physical cutoff family used by the Clay route.
--
-- This is exactly the trust boundary needed for Round84's marked theorem:
--   * beta/source derivatives,
--   * field Hessian derivatives,
--   * composite-source derivatives
-- may reuse the same source localization mechanism once their literal variables
-- are identified with CMP116's analytic coordinates and a common positive radius
-- is established.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact

-- CMP116 Sect. 1 / (1.23)--(1.36): differentiated decoupled local activities
-- retain an exponentially localized analytic representation.
cmp116DifferentiatedActivityLocalizationLevel : ProofLevel
cmp116DifferentiatedActivityLocalizationLevel = standardImported

-- Standard several-complex-variable Cauchy estimate: a k-th derivative on a
-- smaller polydisc costs only the appropriate inverse-radius factor; it does not
-- erase an independent spatial/tree exponential majorant.
finitePolydiscCauchyDerivativePreservesExternalMajorantLevel : ProofLevel
finitePolydiscCauchyDerivativePreservesExternalMajorantLevel = standardImported

-- In-repo `BalabanDecoupledActivityHessian` already performs the exact generic
-- lift from a marked boundary comparison to the Cauchy coefficient/Hessian.
markedBoundaryToHessianCauchyLiftLevel : ProofLevel
markedBoundaryToHessianCauchyLiftLevel = machineChecked

-- The remaining physical L2 seam is narrower than "prove three decay theorems":
-- identify the literal beta-irrelevant-memory, physical-spatial Hessian and
-- composite-source marks with the source analytic coordinates, and prove the
-- required analytic radii/constants are positive and cutoff/volume/scale uniform
-- on the SAME admissible YM trajectory.
physicalCMP116MarkedCoordinateAndUniformRadiusIdentificationLevel : ProofLevel
physicalCMP116MarkedCoordinateAndUniformRadiusIdentificationLevel = conditional
