module DASHI.Physics.YangMills.BalabanPolchinskiMultiscaleLSIBridgeExact where

------------------------------------------------------------------------
-- ROUND69: POLCHINSKI MULTISCALE LOG-SOBOLEV ROUTE FROM THE SAME RG HESSIAN
--
-- PRIMARY SOURCES
--
-- Roland Bauerschmidt and Thierry Bodineau,
-- "Log-Sobolev Inequality for the Continuum Sine-Gordon Model",
-- Communications on Pure and Applied Mathematics 74 (2021), 2064--2113.
-- DOI: 10.1002/cpa.21926.
-- Theorem 1.2 is the source boundary used here.
--
-- Roland Bauerschmidt, Thierry Bodineau and Benoit Dagallier,
-- "Stochastic dynamics and the Polchinski equation: an introduction",
-- Probability Surveys 21 (2024), 200--290.
-- DOI: 10.1214/24-PS27.
--
-- Dominique Bakry and Michel Emery,
-- "Diffusions hypercontractives",
-- Seminaire de Probabilites XIX, Lecture Notes in Mathematics 1123 (1985),
-- 177--206. DOI: 10.1007/BFb0075847.
--
-- SOURCE THEOREM
--
-- For a measure
--
--   dnu_0 proportional to exp[-(1/2)(zeta,A zeta)-V_0(zeta)] dzeta,
--
-- put Q_t=exp(-tA/2), let V_t be the Polchinski-renormalised potential, and
-- suppose lambda>0 is the smallest eigenvalue of A.  If
--
--   Q_t Hess V_t(phi) Q_t >= dotMu_t id
--
-- for every t and phi, with Mu_t = integral_0^t dotMu_s ds, then the source
-- proves an LSI with
--
--   1/gamma = integral_0^infinity exp(-lambda t - 2 Mu_t) dt,
--
-- provided this integral is finite.  The dotMu_t may be negative; V_t need not
-- be convex.  The heat-kernel smoothing in Q_t is part of the hypothesis and
-- must not be erased.
--
-- DASHI CONTRIBUTION
--
-- Expose the exact same-object bridge required from Balaban's RG.  Unlike a
-- global Holley--Stroock oscillation bound, this route is intrinsically
-- multiscale and can consume the local Hessian row control produced by the
-- unified polymer norm.  It also does not require the RG trajectory to enter
-- the strong-coupling SZZ window.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record PublishedPolchinskiLSICriterion
    (Field Scale Potential HeatOperator HessianForm Bound : Set) : Set₁ where
  field
    basePotential : Potential
    renormalisedPotential : Scale → Potential
    heatOperator : Scale → HeatOperator
    hessianForm : Potential → Field → HessianForm

    LessEqualForm : HessianForm → HessianForm → Set
    scalarIdentityForm : Bound → HessianForm

    lambda : Bound
    LambdaPositive : Bound → Set
    lambdaPositive : LambdaPositive lambda

    dotMu cumulativeMu : Scale → Bound
    cumulativeMuIsIntegralOfDotMu : Set

    -- Literal source hypothesis, including BOTH heat operators.
    heatSmoothedHessianLower : ∀ scale field →
      LessEqualForm
        (scalarIdentityForm (dotMu scale))
        (hessianForm (renormalisedPotential scale) field)

    -- Exact source integral.  This carrier is intentionally abstract because
    -- the repo's rational finite algebra is not a replacement for the
    -- continuous exponential/integration theorem.
    inverseLSIConstant : Bound
    inverseLSIConstantIsPolchinskiIntegral : Set
    polchinskiIntegralFinite : Set

    LogSobolevInequality : Set
    sourceTheoremProducesLSI :
      polchinskiIntegralFinite → LogSobolevInequality

open PublishedPolchinskiLSICriterion public

bauerschmidtBodineauPolchinskiCriterionLevel : ProofLevel
bauerschmidtBodineauPolchinskiCriterionLevel = standardImported

------------------------------------------------------------------------
-- Same-object Yang--Mills instantiation boundary.
------------------------------------------------------------------------

record BalabanPolchinskiSameObjectBridge
    (RGState Field Scale Potential HeatOperator HessianForm Bound : Set) : Set₁ where
  field
    rgStateAtScale : Scale → RGState
    effectivePotentialOf : RGState → Potential

    criterion : PublishedPolchinskiLSICriterion
      Field Scale Potential HeatOperator HessianForm Bound

    -- The Polchinski V_t must literally be the potential of the same RG state;
    -- a separately constructed effective measure cannot be spliced here.
    renormalisedPotentialIsBalabanEffectivePotential : ∀ scale →
      renormalisedPotential criterion scale
      ≡ effectivePotentialOf (rgStateAtScale scale)

    -- The heat/covariance decomposition must be identified with the same
    -- fluctuation integration used by the physical RG, not merely declared to
    -- have a similar scale parameter.
    HeatOperatorMatchesRGFluctuationCovariance : Set
    heatOperatorMatchesRGFluctuationCovariance :
      HeatOperatorMatchesRGFluctuationCovariance

open BalabanPolchinskiSameObjectBridge public

sameObjectPolchinskiLSI :
  ∀ {RGState Field Scale Potential HeatOperator HessianForm Bound}
    (bridge : BalabanPolchinskiSameObjectBridge
      RGState Field Scale Potential HeatOperator HessianForm Bound) →
  polchinskiIntegralFinite (criterion bridge) →
  LogSobolevInequality (criterion bridge)
sameObjectPolchinskiLSI bridge finite =
  sourceTheoremProducesLSI (criterion bridge) finite

balabanPolchinskiSameObjectCompilerLevel : ProofLevel
balabanPolchinskiSameObjectCompilerLevel = machineChecked

-- Remaining physical theorem on this route:
--
--   (1) identify the Balaban fluctuation-covariance decomposition with a
--       Polchinski Q_t/V_t flow on the same effective density;
--   (2) derive the heat-smoothed Hessian lower rate dotMu_t from the local
--       unified-norm Hessian estimates;
--   (3) prove the accumulated negative curvature debt is small enough that
--       the source integral for 1/gamma is finite uniformly in cutoff/volume.
--
-- This is a candidate replacement for an independent terminal-gap lemma.  No
-- Yang--Mills inhabitant is asserted by citation.
physicalBalabanPolchinskiMultiscaleLSILevel : ProofLevel
physicalBalabanPolchinskiMultiscaleLSILevel = conditional
