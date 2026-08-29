module DASHI.Physics.YangMills.CompactLieHeatDoobRicciReserveDebtExact where

------------------------------------------------------------------------
-- ROUND74: POSITIVE COMPACT-SIMPLE RICCI RESERVE + CUMULATIVE HESSIAN DEBT
--          -> FINITE HEAT/DOOB LSI INTEGRAL
--
-- PRIMARY / STANDARD SOURCES
--
-- John Milnor,
-- "Curvatures of Left Invariant Metrics on Lie Groups",
-- Advances in Mathematics 21 (1976), 293--329.
-- DOI: 10.1016/S0001-8708(76)80002-3.
-- For a bi-invariant metric Ric = -(1/4) Killing.  On a compact simple factor
-- the Killing form is negative definite, hence for every fixed metric
-- normalization there is a positive rho_G with Ric >= rho_G g.  For the
-- canonical metric g = -B, Ric = (1/4) g.
--
-- Dominique Bakry and Michel Emery,
-- "Diffusions hypercontractives", Seminaire de Probabilites XIX,
-- Lecture Notes in Mathematics 1123 (1985), 177--206.
-- DOI: 10.1007/BFb0075847.
--
-- Jean-Francois Collet and Florent Malrieu,
-- "Logarithmic Sobolev inequalities for inhomogeneous Markov semigroups",
-- ESAIM: Probability and Statistics 12 (2008), 492--504.
-- DOI: 10.1051/ps:2007042.  Preprint: arXiv:math/0602548.
--
-- NORMALIZATION CHECK
--
-- The group heat generator in the current lane is (1/2) Delta.  If V_t = 0
-- and Ric >= rho g then kappa = rho/2, hence
--
--     I = integral_0^infinity exp(-rho t) dt = 1/rho,
--
-- and the convention
--
--     Ent(f^2) <= 2 I E |grad f|^2
--
-- gives the familiar limiting constant 2/rho.  Thus no additional factor two
-- belongs in the current `gamma >= 1/I` convention.
--
-- DASHI REDUCTION
--
-- Let the heat-renormalized potential satisfy
--
--     Hess V_t >= - eta(t) g,        eta(t) >= 0,
--
-- and suppose its accumulated negative Hessian debt is uniformly bounded:
--
--     integral_0^t eta(s) ds <= M     for every t >= 0.
--
-- With Ric >= rho g, rho > 0,
--
--     kappa_t >= rho/2 - eta(t),
--
-- so
--
--     K(t) = integral_0^t kappa_s ds >= (rho/2)t - M,
--
--     exp(-2K(t)) <= exp(2M) exp(-rho t),
--
--     I <= exp(2M)/rho < infinity,
--
-- and therefore
--
--     gamma >= rho exp(-2M) > 0.
--
-- This is the sharp physical boundary for the current #6 route.  We do NOT
-- need an arbitrary favourable curvature history: the new Yang--Mills theorem
-- is a volume/cutoff-uniform bound on cumulative NEGATIVE HESSIAN DEBT of V_t.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieHeatDoobMultiscaleLSIExact as Heat

record RicciReserveHessianDebtData
    (heat : Heat.HeatDoobMultiscaleLSIData) : Set₁ where
  field
    Reserve DebtBound : Set
    reserve : Reserve
    debt : DebtBound

    PositiveReserve : Reserve → Set
    UniformCumulativeNegativeHessianDebt : DebtBound → Set

    reservePositive : PositiveReserve reserve
    debtUniform : UniformCumulativeNegativeHessianDebt debt

    history : Heat.CurvatureTimeBound heat

    -- Standard differential-geometric/calculus consequences of the explicit
    -- inequalities displayed in the header.  They are NOT Yang--Mills inputs.
    reserveAndDebtGiveCurvatureLowerBound :
      PositiveReserve reserve →
      UniformCumulativeNegativeHessianDebt debt →
      Heat.CurvatureLowerBound heat history

    reserveAndDebtGiveFiniteIntegratedWeight :
      PositiveReserve reserve →
      UniformCumulativeNegativeHessianDebt debt →
      Heat.IntegratedCurvatureWeightFinite heat history

open RicciReserveHessianDebtData public

ricciReserveDebtGivesLSI :
  ∀ {heat} →
  (dataSet : RicciReserveHessianDebtData heat) →
  Heat.LogSobolev heat (history dataSet)
ricciReserveDebtGivesLSI {heat} dataSet =
  Heat.heatDoobMultiscaleLSI heat (history dataSet)
    (reserveAndDebtGiveCurvatureLowerBound dataSet
      (reservePositive dataSet) (debtUniform dataSet))
    (reserveAndDebtGiveFiniteIntegratedWeight dataSet
      (reservePositive dataSet) (debtUniform dataSet))

compactSimplePositiveRicciReserveLevel : ProofLevel
compactSimplePositiveRicciReserveLevel = standardImported

reserveDebtEnvelopeToFiniteLSIIntegralLevel : ProofLevel
reserveDebtEnvelopeToFiniteLSIIntegralLevel = standardImported

ricciReserveDebtToLSIAssemblyLevel : ProofLevel
ricciReserveDebtToLSIAssemblyLevel = machineChecked

-- TRUE PHYSICAL LEAF AFTER THE ROUND74 TOP-DOWN REDUCTION:
-- on the SAME literal finite-cutoff Yang--Mills Gibbs density and its group
-- heat/Doob interpolation, bound the cumulative negative part of Hess V_t by a
-- constant independent of lattice volume and cutoff.  CMP109/CMP119
-- quasi-local differentiated bounds and the unified derivative coordinate are
-- the intended inputs.
physicalUniformCumulativeNegativeHessianDebtLevel : ProofLevel
physicalUniformCumulativeNegativeHessianDebtLevel = conditional
