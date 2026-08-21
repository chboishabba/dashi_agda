module DASHI.Physics.YangMills.BalabanClayFrozenFourCompletionContractExact where

------------------------------------------------------------------------
-- FROZEN RESEARCH SCOREBOARD: FOUR MEANS FOUR PHYSICAL THEOREMS
--
-- This file is deliberately not another decomposition round.  It prevents a
-- future implementation from decrementing the research count merely because
-- one downstream compiler, source transcription, or formal-foundation layer
-- was completed.
--
-- A row closes only when an inhabitant of its physical completion predicate is
-- supplied on the literal same-object carrier.
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Dominique Bakry and Michel Emery, "Diffusions hypercontractives",
-- Seminaire de Probabilites XIX, LNM 1123 (1985), 177--206.
-- DOI: 10.1007/BFb0075847.
--
-- Jean-Francois Collet and Florent Malrieu,
-- "Logarithmic Sobolev inequalities for inhomogeneous Markov semigroups",
-- ESAIM: Probability and Statistics 12 (2008), 492--504.
-- DOI: 10.1051/ps:2007042.
--
-- Roland Bauerschmidt and Thierry Bodineau,
-- "Log-Sobolev Inequality for the Continuum Sine-Gordon Model",
-- CPAM 74 (2021), 2064--2113. DOI: 10.1002/cpa.21926.
-- The BBD covariance-weighted criterion is retained as an ALTERNATE LINEAR-
-- FIELD route only; it is not definitionally the compact-group Heat/Doob
-- criterion used by row C.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _≤ℝ_; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory as Trajectory
import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra as Interval
import DASHI.Physics.YangMills.BalabanRenormalisedCouplingExistence as Renorm
import DASHI.Physics.YangMills.CompactLieHeatDoobMultiscaleLSIExact as HeatDoob
import DASHI.Physics.YangMills.BalabanPolchinskiMultiscaleLSIBridgeExact as BBD

------------------------------------------------------------------------
-- A. POSITIVE / TUNED LITERAL BETA TRAJECTORY
------------------------------------------------------------------------

-- A positive cumulative slope is not the same theorem as the one-sided prefix
-- majorant consumed by the inverse-square small-coupling budget.  Conversely,
-- a positive cumulative slope does not construct the tuned bare coupling.
-- Row A therefore requires BOTH on the same generated dynamics.
record LiteralCompactSimplePositiveBetaCompletion : Set₁ where
  field
    construction : Renorm.BalabanRenormalisedCouplingConstruction

    lowerSlope upperSlope : ℝ
    lowerSlopePositive : 0ℝ <ℝ lowerSlope
    lowerSlopeBelowUpperSlope : lowerSlope ≤ℝ upperSlope

    lowerLinear upperLinear : Nat → ℝ
    lowerLinearZero : lowerLinear zero ≡ 0ℝ
    upperLinearZero : upperLinear zero ≡ 0ℝ
    lowerLinearStep : ∀ n →
      lowerLinear (suc n) ≡ lowerLinear n +ℝ lowerSlope
    upperLinearStep : ∀ n →
      upperLinear (suc n) ≡ upperLinear n +ℝ upperSlope

    -- Every finite interval of the SAME literal cutoff trajectory has the
    -- source-required bilateral linear beta tube.  The interval [k,k+n]
    -- consists of shells k+1,...,k+n.
    betaIntervalBilateral :
      ∀ K k n → k + n ≤ K →
      lowerLinear n ≤ℝ
        Interval.intervalSum
          (Trajectory.betaCorrection
            (BetaLaw.step (Renorm.dynamics construction K)))
          k n
      ×
      Interval.intervalSum
        (Trajectory.betaCorrection
          (BetaLaw.step (Renorm.dynamics construction K)))
        k n
        ≤ℝ upperLinear n

open LiteralCompactSimplePositiveBetaCompletion public

-- A row-A inhabitant automatically contains the already-required tuned,
-- nonvanishing physical coupling window.  This projection is intentionally
-- trivial: the hard work is constructing the inhabitant, not repackaging it.
rowAHasRenormalisedTrajectory :
  LiteralCompactSimplePositiveBetaCompletion →
  Renorm.BalabanRenormalisedCouplingConstruction
rowAHasRenormalisedTrajectory = construction

------------------------------------------------------------------------
-- C. COMPACT-GROUP HEAT/DOOB COMPLETION, NOT AN UNWEIGHTED BBD IMPORT
------------------------------------------------------------------------

-- The primary compact-group route is the literal Laplace--Beltrami Heat/Doob
-- flow on G^E.  Its curvature statement is
--
--       1/2 Ric + Hess V_t >= kappa_t g,
--
-- with finite integrated negative debt, followed on the SAME density by the
-- physical spatial influence estimate.  If one instead chooses the linear
-- Gaussian BBD/Polchinski route, its actual hypothesis is
--
--   dotC Hess(V_t) dotC - 1/2 ddotC >= dotEll dotC,
--
-- and a separate chart/globalisation theorem is mandatory.  The two routes
-- are therefore deliberately separate types below.
record SameDensityCompactLieHeatDoobMassGapCompletion
    (dataSet : HeatDoob.HeatDoobMultiscaleLSIData) : Set₁ where
  field
    history : HeatDoob.CurvatureTimeBound dataSet
    literalSameDensityIdentification : Set
    curvatureLower : HeatDoob.CurvatureLowerBound dataSet history
    integratedCurvatureWeightFinite :
      HeatDoob.IntegratedCurvatureWeightFinite dataSet history
    physicalCovariantInfluencePropagation : Set
    uniformExponentialConnectedClustering : Set

open SameDensityCompactLieHeatDoobMassGapCompletion public

record AlternateBBDGaugeChartCompletion
    (RGState Field Scale Potential CovarianceOperator HessianForm Bound : Set)
    : Set₁ where
  field
    bridge : BBD.BalabanPolchinskiSameObjectBridge
      RGState Field Scale Potential CovarianceOperator HessianForm Bound
    weightedPolchinskiCriterionFinite :
      BBD.polchinskiIntegralFinite (BBD.criterion bridge)

open AlternateBBDGaugeChartCompletion public

-- This projection witnesses the exact generic consequence used by the primary
-- C route.  It does NOT manufacture the physical curvature or spatial bound.
rowCHeatDoobGivesLSI :
  ∀ {dataSet}
    (completion : SameDensityCompactLieHeatDoobMassGapCompletion dataSet) →
  HeatDoob.LogSobolev dataSet (history completion)
rowCHeatDoobGivesLSI {dataSet} completion =
  HeatDoob.heatDoobMultiscaleLSI dataSet
    (history completion)
    (curvatureLower completion)
    (integratedCurvatureWeightFinite completion)

------------------------------------------------------------------------
-- SCOREBOARD AUTHORITY
------------------------------------------------------------------------

frozenClayResearchFamilyCount : Nat
frozenClayResearchFamilyCount = 4

-- The count remains four here.  A new root may decrement it only by importing
-- an actual inhabitant of one complete physical row (A/B/C/D), or a theorem
-- proving that one complete row follows from another.  No conditional field is
-- promoted in this module.
rowACompletionLevel : ProofLevel
rowACompletionLevel = conditional

rowBCompletionLevel : ProofLevel
rowBCompletionLevel = conditional

rowCCompletionLevel : ProofLevel
rowCCompletionLevel = conditional

rowDCompletionLevel : ProofLevel
rowDCompletionLevel = conditional
