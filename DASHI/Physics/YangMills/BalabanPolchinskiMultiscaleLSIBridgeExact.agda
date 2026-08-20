module DASHI.Physics.YangMills.BalabanPolchinskiMultiscaleLSIBridgeExact where

------------------------------------------------------------------------
-- ROUND73: EXACT BBD POLCHINSKI SOURCE BOUNDARY -- LINEAR FIELD SPACE ONLY
--
-- PRIMARY SOURCES
--
-- Roland Bauerschmidt and Thierry Bodineau,
-- "Log-Sobolev Inequality for the Continuum Sine-Gordon Model",
-- Communications on Pure and Applied Mathematics 74 (2021), 2064--2113.
-- DOI: 10.1002/cpa.21926. arXiv:1907.12308.
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
-- CRITICAL CARRIER BOUNDARY
--
-- BBD Theorem 1.2 begins with a LINEAR field space X subset R^N, a positive
-- matrix A, and Gaussian covariance convolution.  It does NOT directly state a
-- theorem for the compact lattice-gauge carrier G^E.  Therefore this module is
-- retained as an exact source theorem / possible gauge-chart route, but it may
-- not be promoted to a physical Yang--Mills LSI unless a separate globalisation
-- theorem identifies the literal measure with an admissible linear/Gaussian
-- Polchinski carrier.
--
-- The primary compact-group route is now
-- `CompactLieHeatDoobMultiscaleLSIExact`, which uses the Haar/Laplace--Beltrami
-- heat semigroup directly on G^E.  That route must prove its own curvature
-- history and is not claimed to follow from BBD automatically.
--
-- SOURCE THEOREM -- EXACT SHAPE RETAINED
--
-- For the BBD linear/Gaussian carrier the source criterion controls
--
--   dotC_t Hess(V_t) dotC_t - (1/2) ddotC_t
--     >= dotEll_t dotC_t
--
-- and a finite source integral yields LSI.  Negative dotEll_t is allowed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record PublishedPolchinskiLSICriterion
    (Field Scale Potential CovarianceOperator HessianForm Bound : Set) : Set₁ where
  field
    basePotential : Potential
    renormalisedPotential : Scale → Potential

    covariance : Scale → CovarianceOperator
    dotCovariance : Scale → CovarianceOperator
    ddotCovariance : Scale → CovarianceOperator

    hessian : Potential → Field → HessianForm
    sandwich : CovarianceOperator → HessianForm → CovarianceOperator → HessianForm
    halfSecondCovarianceForm : CovarianceOperator → HessianForm
    subtractForm : HessianForm → HessianForm → HessianForm
    scalarTimesCovarianceForm : Bound → CovarianceOperator → HessianForm
    LessEqualForm : HessianForm → HessianForm → Set

    dotEll cumulativeEll : Scale → Bound
    cumulativeEllIsIntegralOfDotEll : Set

    multiscaleBakryEmeryLower : ∀ scale field →
      LessEqualForm
        (scalarTimesCovarianceForm (dotEll scale) (dotCovariance scale))
        (subtractForm
          (sandwich
            (dotCovariance scale)
            (hessian (renormalisedPotential scale) field)
            (dotCovariance scale))
          (halfSecondCovarianceForm (ddotCovariance scale)))

    inverseLSIConstant : Bound
    inverseLSIConstantIsSourceIntegral : Set
    polchinskiIntegralFinite : Set

    LogSobolevInequality : Set
    sourceTheoremProducesLSI :
      polchinskiIntegralFinite → LogSobolevInequality

open PublishedPolchinskiLSICriterion public

bauerschmidtBodineauPolchinskiCriterionLevel : ProofLevel
bauerschmidtBodineauPolchinskiCriterionLevel = standardImported

record HeatSmoothedPresentation
    {Field Scale Potential CovarianceOperator HessianForm Bound}
    (criterion : PublishedPolchinskiLSICriterion
      Field Scale Potential CovarianceOperator HessianForm Bound)
    (HeatOperator : Set) : Set₁ where
  field
    heatOperator : Scale → HeatOperator
    heatSmoothedHessianForm :
      HeatOperator → Potential → Field → HessianForm
    heatSmoothedLowerForm : Scale → Field → HessianForm

    exactCovarianceRewrite : ∀ scale field →
      heatSmoothedLowerForm scale field
      ≡ subtractForm criterion
          (sandwich criterion
            (dotCovariance criterion scale)
            (hessian criterion
              (renormalisedPotential criterion scale) field)
            (dotCovariance criterion scale))
          (halfSecondCovarianceForm criterion
            (ddotCovariance criterion scale))

    heatSmoothedPresentationExact : ∀ scale field →
      heatSmoothedHessianForm
        (heatOperator scale)
        (renormalisedPotential criterion scale)
        field
      ≡ heatSmoothedLowerForm scale field

open HeatSmoothedPresentation public

------------------------------------------------------------------------
-- Optional Yang--Mills chart/globalisation route.
------------------------------------------------------------------------

record BalabanPolchinskiSameObjectBridge
    (RGState Field Scale Potential CovarianceOperator HessianForm Bound : Set)
    : Set₁ where
  field
    rgStateAtScale : Scale → RGState
    effectivePotentialOf : RGState → Potential
    fluctuationCovarianceOf : RGState → CovarianceOperator

    criterion : PublishedPolchinskiLSICriterion
      Field Scale Potential CovarianceOperator HessianForm Bound

    -- CRITICAL: this bridge is meaningful physically only after `Field` has
    -- been proved to be the admissible LINEAR chart/globalised carrier required
    -- by the BBD theorem, including the measure/Jacobian and large-field pieces.
    LinearGaussianCarrierGlobalisesLiteralGaugeMeasure : Set
    linearGaussianCarrierGlobalisesLiteralGaugeMeasure :
      LinearGaussianCarrierGlobalisesLiteralGaugeMeasure

    renormalisedPotentialIsBalabanEffectivePotential : ∀ scale →
      renormalisedPotential criterion scale
      ≡ effectivePotentialOf (rgStateAtScale scale)

    covarianceIsBalabanFluctuationCovariance : ∀ scale →
      covariance criterion scale
      ≡ fluctuationCovarianceOf (rgStateAtScale scale)

    DotCovarianceMatchesRGScaleDerivative : Set
    DDotCovarianceMatchesRGScaleDerivative : Set
    dotCovarianceMatchesRGScaleDerivative :
      DotCovarianceMatchesRGScaleDerivative
    ddotCovarianceMatchesRGScaleDerivative :
      DDotCovarianceMatchesRGScaleDerivative

open BalabanPolchinskiSameObjectBridge public

sameObjectPolchinskiLSI :
  ∀ {RGState Field Scale Potential CovarianceOperator HessianForm Bound}
    (bridge : BalabanPolchinskiSameObjectBridge
      RGState Field Scale Potential CovarianceOperator HessianForm Bound) →
  polchinskiIntegralFinite (criterion bridge) →
  LogSobolevInequality (criterion bridge)
sameObjectPolchinskiLSI bridge finite =
  sourceTheoremProducesLSI (criterion bridge) finite

balabanPolchinskiSameObjectCompilerLevel : ProofLevel
balabanPolchinskiSameObjectCompilerLevel = machineChecked

-- No direct compact-group promotion is permitted from this module.
physicalEuclideanChartGlobalisationForBBDLevel : ProofLevel
physicalEuclideanChartGlobalisationForBBDLevel = conditional

-- If a future proof supplies that globalisation, the remaining BBD route still
-- needs the exact covariance derivatives, curvature bound and finite debt.
physicalBalabanPolchinskiMultiscaleLSILevel : ProofLevel
physicalBalabanPolchinskiMultiscaleLSILevel = conditional
