module DASHI.Physics.YangMills.CompactLieHeatDoobMultiscaleLSIExact where

------------------------------------------------------------------------
-- ROUND73: GROUP-NATIVE HEAT/DOOB MULTISCALE LOG-SOBOLEV CRITERION
--
-- MOTIVATION / CARRIER CORRECTION
--
-- Roland Bauerschmidt and Thierry Bodineau,
-- "Log-Sobolev Inequality for the Continuum Sine-Gordon Model",
-- Communications on Pure and Applied Mathematics 74 (2021), 2064--2113.
-- DOI: 10.1002/cpa.21926. arXiv:1907.12308.
-- Their Polchinski criterion is formulated on a LINEAR field space X subset
-- R^N with Gaussian covariance convolution.  It is excellent calibration, but
-- it cannot be applied literally to the lattice gauge carrier G^E without a
-- separate chart/globalisation theorem.
--
-- The literal compact-group carrier has a more natural semigroup: the
-- Laplace--Beltrami heat semigroup of the bi-invariant metric/Haar measure.
-- This file records the exact inhomogeneous Doob-flow criterion on that carrier.
--
-- STANDARD GEOMETRIC/SEMIGROUP SOURCES
--
-- Dominique Bakry and Michel Emery,
-- "Diffusions hypercontractives", Seminaire de Probabilites XIX,
-- Lecture Notes in Mathematics 1123 (1985), 177--206.
-- DOI: 10.1007/BFb0075847.
--
-- Jean-Francois Collet and Florent Malrieu,
-- "Logarithmic Sobolev inequalities for inhomogeneous Markov semigroups",
-- ESAIM: Probability and Statistics 12 (2008), 492--504.
-- DOI: 10.1051/ps:2007042.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction",
-- second edition, GTM 222, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- MATHEMATICAL STATEMENT
--
-- Let (M,g,m) be compact with m normalized, H_t = exp(t Delta/2), and
--
--     u_t = H_t(exp(-V_0)),        V_t = -log u_t,
--     nu_t = u_t m / Z,
--     F_t = H_t(exp(-V_0) F) / u_t.
--
-- Then
--
--     d/dt F_t = (1/2 Delta - grad V_t . grad) F_t,
--
-- and relative entropy of the two heat flows satisfies
--
--   -d/dt Ent_{nu_t}(F_t)
--       = 1/2 E_{nu_t} [ |grad F_t|^2 / F_t ].              (E)
--
-- The Bochner identity for this time-dependent Doob generator gives
--
--   (partial_t-L_t)|grad F_t|^2
--      <= -2 kappa_t |grad F_t|^2                           (G)
--
-- whenever
--
--       1/2 Ric + Hess V_t >= kappa_t g.                    (C)
--
-- Therefore, writing K(t)=integral_0^t kappa_s ds,
--
--   |grad F_t| <= exp(-K(t)) P_{0,t}|grad F|.
--
-- Markov Cauchy--Schwarz then gives
--
--   |grad F_t|^2/F_t
--      <= exp(-2K(t)) P_{0,t}(|grad F|^2/F).
--
-- Since E_{nu_t} P_{0,t} = E_{nu_0}, integration of (E) and ergodicity of
-- compact heat flow imply
--
--   Ent_{nu_0}(F)
--      <= 1/2 I E_{nu_0}(|grad F|^2/F),
--
--   I = integral_0^infinity exp(-2K(t)) dt.
--
-- Equivalently, for F=f^2,
--
--   Ent_{nu_0}(f^2) <= 2 I E_{nu_0}|grad f|^2,
--
-- so the log-Sobolev constant satisfies gamma >= 1/I whenever I<infinity.
--
-- This is the correct compact-Lie multiscale target for the YM mass-gap lane.
-- It retains the same conceptual advantage as the Polchinski criterion:
-- kappa_t may be negative on some scales, provided the accumulated curvature
-- debt still makes I finite.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact theorem boundary.
--
-- The differential-geometric identities below are standard Riemannian heat /
-- Gamma-calculus facts.  DASHI does NOT import the Euclidean BBD theorem as if
-- it were a compact-group theorem.  The new Yang--Mills-specific task is to
-- bound the SAME heat-renormalised potential V_t on G^E using the already
-- source-owned CMP109/CMP119 quasi-local effective-action estimates.
------------------------------------------------------------------------

record HeatDoobMultiscaleLSIData : Set₁ where
  field
    PositiveFunction Observable CurvatureTimeBound : Set

    -- Named standard analytic statements on the literal compact manifold.
    heatLogTransformHamiltonJacobi : Set
    doobGeneratorIdentity : Set
    relativeEntropyDissipation : Set
    bochnerDoobGradientInequality : Set
    markovCauchySchwarz : Set
    compactHeatErgodicity : Set

    -- Quantitative curvature history and its integrability.
    CurvatureLowerBound : CurvatureTimeBound → Set
    IntegratedCurvatureWeightFinite : CurvatureTimeBound → Set

    -- LSI conclusion for the initial Gibbs measure.
    LogSobolev : CurvatureTimeBound → Set

    curvatureHistoryImpliesLSI : ∀ history →
      CurvatureLowerBound history →
      IntegratedCurvatureWeightFinite history →
      LogSobolev history

open HeatDoobMultiscaleLSIData public

heatDoobMultiscaleLSI :
  (dataSet : HeatDoobMultiscaleLSIData) →
  ∀ history →
  CurvatureLowerBound dataSet history →
  IntegratedCurvatureWeightFinite dataSet history →
  LogSobolev dataSet history
heatDoobMultiscaleLSI dataSet = curvatureHistoryImpliesLSI dataSet

-- The generic inhomogeneous Gamma-calculus theorem is conventional analysis,
-- not a Yang--Mills research premise.  The exact carrier is compact Riemannian,
-- unlike the Euclidean Gaussian Polchinski criterion.
compactRiemannianHeatDoobCriterionLevel : ProofLevel
compactRiemannianHeatDoobCriterionLevel = standardImported

-- Physical YM seam: on the SAME finite-cutoff effective density, construct the
-- heat-renormalised potential V_t on G^E and prove a volume-uniform lower bound
-- for
--
--       1/2 Ric + Hess V_t
--
-- with integrable accumulated negative curvature debt.  The source-owned
-- CMP109 differentiated decay / CMP119 complete-density bounds are the natural
-- quasi-local inputs; no Euclidean chart identification is assumed here.
physicalYMHeatDoobCurvatureHistoryLevel : ProofLevel
physicalYMHeatDoobCurvatureHistoryLevel = conditional

-- Once the LSI/Poincare rate is produced on the literal group Gibbs measure,
-- the existing weighted-Hessian finite-speed route converts temporal relaxation
-- to spatial covariance decay before OS reconstruction.
physicalYMHeatDoobToSpatialClusteringLevel : ProofLevel
physicalYMHeatDoobToSpatialClusteringLevel = conditional
