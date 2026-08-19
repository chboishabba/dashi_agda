module DASHI.Physics.YangMills.BalabanPolchinskiMultiscaleLSIBridgeExact where

------------------------------------------------------------------------
-- ROUND70: EXACT POLCHINSKI MULTISCALE LOG-SOBOLEV SOURCE BOUNDARY
--
-- PRIMARY SOURCES
--
-- Roland Bauerschmidt and Thierry Bodineau,
-- "Log-Sobolev Inequality for the Continuum Sine-Gordon Model",
-- Communications on Pure and Applied Mathematics 74 (2021), 2064--2113.
-- DOI: 10.1002/cpa.21926. arXiv:1907.12308.
-- Multiscale Bakry--Emery criterion: Theorem 2.5 in the published numbering.
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
-- SOURCE THEOREM -- EXACT SHAPE RETAINED
--
-- Let C_t be the covariance decomposition used in the Polchinski flow and V_t
-- the corresponding renormalised potential.  The source criterion controls
--
--   dotC_t Hess(V_t) dotC_t - (1/2) ddotC_t
--     >= dotEll_t dotC_t
--
-- as a quadratic-form inequality, for every t and field.  If the associated
-- source integral is finite, the initial measure satisfies an LSI.  Negative
-- dotEll_t is allowed: the criterion is multiscale and does not demand global
-- log-concavity at every scale.
--
-- A frequently convenient heat-semigroup presentation is a SPECIALISATION of
-- this covariance criterion, not its definition.  Round70 therefore keeps the
-- literal dotC/ddotC form as the authority surface and makes any Q_t rewrite an
-- explicit same-object theorem.
--
-- DASHI CONTRIBUTION
--
-- Expose the exact SAME-OBJECT Yang--Mills seam.  The Balaban fluctuation
-- covariance, its first/second scale derivatives, and the Polchinski V_t must
-- be identified with the objects in this criterion.  A bare Hessian estimate
-- or a separately constructed stochastic measure cannot be spliced in.
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

    -- Literal Bauerschmidt--Bodineau multiscale curvature hypothesis:
    --
    --   dotC Hess(V_t) dotC - 1/2 ddotC >= dotEll dotC.
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

------------------------------------------------------------------------
-- Optional heat/smoothed-Hessian presentation.  This is deliberately a
-- theorem-bearing rewrite of the exact criterion rather than a replacement.
------------------------------------------------------------------------

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
-- Same-object Yang--Mills instantiation boundary.
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

    renormalisedPotentialIsBalabanEffectivePotential : ∀ scale →
      renormalisedPotential criterion scale
      ≡ effectivePotentialOf (rgStateAtScale scale)

    covarianceIsBalabanFluctuationCovariance : ∀ scale →
      covariance criterion scale
      ≡ fluctuationCovarianceOf (rgStateAtScale scale)

    -- Derivative/coherence data must be for the SAME covariance path.  They are
    -- kept explicit because merely matching C_t pointwise does not identify its
    -- scale derivatives without a differentiability/coherence theorem.
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

-- Remaining physical work on this route is now exactly source-shaped:
--
-- (1) identify Balaban's fluctuation covariance C_t and its scale derivatives
--     with the Polchinski C_t, dotC_t, ddotC_t on the SAME effective density;
-- (2) prove the literal multiscale quadratic-form lower bound above from the
--     unified local derivative/Hessian estimates;
-- (3) prove the accumulated negative curvature debt makes the source integral
--     finite uniformly in cutoff/volume;
-- (4) separately obtain spatial derivative propagation before promoting the
--     stochastic functional inequality to Euclidean clustering/physical gap.
physicalBalabanPolchinskiMultiscaleLSILevel : ProofLevel
physicalBalabanPolchinskiMultiscaleLSILevel = conditional
