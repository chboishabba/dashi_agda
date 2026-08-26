module DASHI.EverythingTopDownObservationCalculus where

------------------------------------------------------------------------
-- TOP-DOWN OBSERVATION / FIBRE / RESIDUAL SPINE
------------------------------------------------------------------------

-- Static observation/refinement and exact consumer descent/minimal quotient.
import DASHI.Core.ObserverRefinementLatticeExact
import DASHI.Core.ObserverFactorizedRefinementExact
import DASHI.Core.ConsumerDescentMinimalObserverExact
import DASHI.Core.ConsumerKernelQuotientPresentationExact
import DASHI.Core.ConsumerQuotientBaseChangeExact
import DASHI.Core.ConsumerQuotientBaseChangeRegression
import DASHI.Core.ConsumerIndexedResidualRefinementExact
import DASHI.Core.TopDownObservationCalculusExact

-- Residual dependency, certified quadratic control, future-language capability,
-- and the independent pressure axis.  Receipt-backed SensibLaw residual order
-- now maps monotonically into the pressure component of the healing preorder.
import DASHI.Core.ResidualObserverDependencyExact
import DASHI.Core.ResidualObserverDependencyRegression
import DASHI.Core.ResidualObserverQuadraticControlExact
import DASHI.Core.FutureLanguageQuadraticControlExact
import DASHI.Core.PressureQuadraticHealingExact
import DASHI.Interop.SensibLawPressureHealingBridgeExact
import DASHI.Mathematics.LinearAlgebra.FiniteRationalQuadraticDominationExact
import DASHI.Mathematics.LinearAlgebra.AffineSpectralIndependenceQuadraticExact

-- Context-indexed carriers and exact finite regression.
import DASHI.Core.ContextIndexedObservationFibrationExact
import DASHI.Core.ContextIndexedObservationFibrationRegression

-- Collision-fibre symmetry, orbit/stabilizer residuals and exact ternary cases.
import DASHI.Core.ResidualSymmetryCollisionFibreExact
import DASHI.Core.ResidualSymmetryCollisionFibreRegression
import DASHI.Core.OrbitStabilizerResidualPresentationExact
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact

-- Exact reopening with uniform and state-dependent residuals.
import DASHI.Core.DependentRecoverableProjectionExact
import DASHI.Core.RecoverableQuotientCompositionExact
import DASHI.Core.RecoverableObserverRefinementTowerExact
import DASHI.Core.SectionedProjectionProvenanceBridgeExact

-- Native ternary minimality and exact optimal-width T^9 binary-locality result.
import DASHI.Foundations.TernaryNativeMinimalityExact
import DASHI.Foundations.TernaryNineOptimalBinaryDilationExact

-- Existing canonical future-language minimality / dynamical realization.
import DASHI.Core.FutureObservationLanguageQuotientExact
import DASHI.Governance.MinimalSufficientObservationGovernanceExact
import DASHI.Cognition.PNF.CanonicalFutureMinimalDynamicalRealizationExact

-- Existing higher-arity/local restriction and authority boundaries.
import DASHI.Reasoning.TypedHyperfabricCore
import DASHI.Cognition.PNF.ObserverSeparationAuthorityBoundaryExact

------------------------------------------------------------------------
-- Aggregate boundary
--
-- A consumer-relevant collision forces every sufficient repair to split it.
-- Static consumer sufficiency != exact reconstruction.
-- Static minimal observer != future-language minimal quotient.
-- Current observation equality != action-indexed dependency equality.
-- Low coupling score != action admissibility.
-- Finite dependency score != affine spectral independence / SDP certificate.
-- Certified quadratic domination != proof that a supplied form is an actual
-- Bansal--Jiang covariance/probe/SDP object.
-- Residual/pressure improvement != certified dependency improvement; the axes
-- are kept separate in a product preorder.
-- Capability preservation remains independent of both minimization axes.
-- A required future trace is one capability constructor, not the only one.
-- Residual labels still require receipts; the pressure bridge assigns none.
-- Context-local adequacy != natural/base-change transport.
-- Symmetry-preserving collision fibre != automatic spectral decomposition.
-- Orbit quotient != exact reconstruction without residual/stabilizer data.
-- Storage-optimal binary != one-bit local binary.
-- Compact binary != necessarily unbounded locality distortion.
-- Sector separation != semantic/world authority.
------------------------------------------------------------------------
