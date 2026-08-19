module DASHI.Physics.YangMills.BalabanPolchinskiMultiscaleLSIBridgeExact where

------------------------------------------------------------------------
-- ROUND69: POLCHINSKI MULTISCALE LOG-SOBOLEV ROUTE FROM THE SAME RG HESSIAN
--
-- PRIMARY SOURCES
--
-- Roland Bauerschmidt and Thierry Bodineau,
-- "Log-Sobolev Inequality for the Continuum Sine-Gordon Model",
-- Communications on Pure and Applied Mathematics 74 (2021), 2064--2113.
-- DOI: 10.1002/cpa.21926.  Theorem 1.2.
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
-- For dnu_0 proportional to exp[-(1/2)(zeta,A zeta)-V_0(zeta)] dzeta, put
-- Q_t=exp(-tA/2).  If
--
--   Q_t Hess V_t(phi) Q_t >= dotMu_t id
--
-- for every t and phi, Mu_t=integral_0^t dotMu_s ds, and lambda>0 is the
-- smallest eigenvalue of A, Bauerschmidt--Bodineau prove an LSI with
--
--   1/gamma = integral_0^infinity exp(-lambda t - 2 Mu_t) dt
--
-- when this integral is finite.  dotMu_t may be negative and V_t need not be
-- convex; the Q_t smoothing is an essential part of the criterion.
--
-- DASHI CONTRIBUTION
--
-- Preserve that exact source shape and expose the SAME-OBJECT Yang--Mills
-- instantiation boundary.  This route is multiscale and can consume local
-- Hessian control from L7 without requiring the Balaban trajectory to cross
-- the fixed-lattice SZZ strong-coupling window.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record PublishedPolchinskiLSICriterion
    (Field Scale Potential HeatOperator HessianForm Bound : Set) : Set₁ where
  field
    basePotential : Potential
    renormalisedPotential : Scale → Potential
    heatOperator : Scale → HeatOperator

    -- This operation literally represents Q Hess(V) Q.  Keeping Q as an
    -- argument prevents a bare-Hessian estimate from being silently promoted
    -- to the source theorem's smoothed hypothesis.
    heatSmoothedHessianForm :
      HeatOperator → Potential → Field → HessianForm

    LessEqualForm : HessianForm → HessianForm → Set
    scalarIdentityForm : Bound → HessianForm

    lambda : Bound
    LambdaPositive : Bound → Set
    lambdaPositive : LambdaPositive lambda

    dotMu cumulativeMu : Scale → Bound
    cumulativeMuIsIntegralOfDotMu : Set

    heatSmoothedHessianLower : ∀ scale field →
      LessEqualForm
        (scalarIdentityForm (dotMu scale))
        (heatSmoothedHessianForm
          (heatOperator scale)
          (renormalisedPotential scale)
          field)

    inverseLSIConstant : Bound
    inverseLSIConstantIsPolchinskiIntegral : Set
    polchinskiIntegralFinite : Set

    LogSobolevInequality : Set
    sourceTheoremProducesLSI :
      polchinskiIntegralFinite → LogSobolevInequality

open PublishedPolchinskiLSICriterion public

bauerschmidtBodineauPolchinskiCriterionLevel : ProofLevel
bauerschmidtBodineauPolchinskiCriterionLevel = standardImported

record BalabanPolchinskiSameObjectBridge
    (RGState Field Scale Potential HeatOperator HessianForm Bound : Set) : Set₁ where
  field
    rgStateAtScale : Scale → RGState
    effectivePotentialOf : RGState → Potential

    criterion : PublishedPolchinskiLSICriterion
      Field Scale Potential HeatOperator HessianForm Bound

    renormalisedPotentialIsBalabanEffectivePotential : ∀ scale →
      renormalisedPotential criterion scale
      ≡ effectivePotentialOf (rgStateAtScale scale)

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

-- Physical work on this route is now exactly:
-- (1) identify the Balaban fluctuation covariance decomposition with Q_t/V_t;
-- (2) prove the smoothed Hessian lower rate from the same unified RG norm;
-- (3) bound accumulated negative curvature debt strongly enough that the
--     published Polchinski integral is finite uniformly in cutoff/volume.
physicalBalabanPolchinskiMultiscaleLSILevel : ProofLevel
physicalBalabanPolchinskiMultiscaleLSILevel = conditional
