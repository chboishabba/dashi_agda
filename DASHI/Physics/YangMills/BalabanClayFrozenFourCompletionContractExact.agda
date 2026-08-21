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
-- John Milnor, "Curvatures of Left Invariant Metrics on Lie Groups",
-- Advances in Mathematics 21 (1976), 293--329.
-- DOI: 10.1016/S0001-8708(76)80002-3.
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
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_+_)
open import Data.Product using (_×_)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _≤ℝ_; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory as Trajectory
import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra as Interval
import DASHI.Physics.YangMills.BalabanRenormalisedCouplingExistence as Renorm
import DASHI.Physics.YangMills.CompactLieHeatDoobMultiscaleLSIExact as HeatDoob
import DASHI.Physics.YangMills.CompactLieHeatDoobRicciReserveDebtExact as Reserve
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

    -- The source running-coupling tube is a TERMINAL-TAIL statement.  For a
    -- cutoff K and a decomposition K = k+n, the relevant beta sum consists of
    -- shells k+1,...,K.  Requiring every internal subinterval would be strictly
    -- stronger than Bałaban's consumer needs; the separate prefix majorant
    -- already carried by `construction` controls smallness from the bare end.
    betaTerminalTailBilateral :
      ∀ K k n → k + n ≡ K →
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
-- flow on G^E.  The already-proved generic reduction says that
--
--   Ric >= rho g, rho > 0,
--   Hess V_t >= -eta(t) g,
--   integral_0^t eta <= M
--
-- imply
--
--   I <= exp(2M)/rho,      gamma_LSI >= rho exp(-2M) > 0.
--
-- Thus the Yang--Mills-specific temporal leaf is the SAME-density, cutoff- and
-- volume-uniform cumulative negative Hessian debt.  Spatial mass-gap closure
-- additionally requires the physical covariant influence estimate on that
-- same density.
--
-- If one instead chooses the linear Gaussian BBD/Polchinski route, its actual
-- hypothesis is
--
--   dotC Hess(V_t) dotC - 1/2 ddotC >= dotEll dotC,
--
-- and a separate chart/globalisation theorem is mandatory.  The two routes
-- are deliberately separate types below.
record SameDensityCompactLieHeatDoobMassGapCompletion
    (dataSet : HeatDoob.HeatDoobMultiscaleLSIData) : Set₁ where
  field
    literalSameDensityIdentification : Set
    reserveAndHessianDebt : Reserve.RicciReserveHessianDebtData dataSet
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
-- C route.  It does NOT manufacture the physical Hessian debt or spatial bound.
rowCHeatDoobGivesLSI :
  ∀ {dataSet}
    (completion : SameDensityCompactLieHeatDoobMassGapCompletion dataSet) →
  HeatDoob.LogSobolev dataSet
    (Reserve.history (reserveAndHessianDebt completion))
rowCHeatDoobGivesLSI completion =
  Reserve.ricciReserveDebtGivesLSI (reserveAndHessianDebt completion)

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
