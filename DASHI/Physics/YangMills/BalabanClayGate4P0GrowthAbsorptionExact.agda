module DASHI.Physics.YangMills.BalabanClayGate4P0GrowthAbsorptionExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT4RunningCouplingConventionBridgeExact as Running

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban, "Large Field Renormalization. II. Localization,
-- Exponentiation, and Bounds for the R Operation", Communications in
-- Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- Primary-source targets pending direct verification:
-- Section 1.4, p. 362, for the chosen growth condition on p0(g);
-- equation (1.89), p. 387, for the T-operation suppression;
-- equation (1.100), p. 388, for the R-operation suppression;
-- Theorem 1, p. 388, for invariant-domain preservation.
--
-- The unreviewed Eriksson interface document is a locator only.  It is not an
-- admissible authority for the inequalities below.
--
-- Existing DASHI reuse: the running coupling must be supplied through the
-- convention-matched recursion of
-- BalabanClayT4RunningCouplingConventionBridgeExact; this module does not
-- create a second beta-function convention.
------------------------------------------------------------------------

record P0SuperlinearLogGrowth
    (Scale Scalar : Set) : Set₁ where
  field
    runningCoupling : Running.ConventionMatchedRunningCoupling Scale Scalar

    p0 couplingMagnitude logMagnitude : Scale → Scalar
    c0 epsilon0 one : Scalar
    add multiply power : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    SmallCoupling : Scale → Set
    epsilon0Positive : Set
    primarySectionOneFourChecked : Set

    p0GrowthDefinition : ∀ scale →
      SmallCoupling scale →
      LessEqual
        (multiply c0
          (power (logMagnitude scale) (add one epsilon0)))
        (p0 scale)

open P0SuperlinearLogGrowth public

------------------------------------------------------------------------
-- F1--F4: collapse the absorption proof into two analytic inequalities and
-- prove the final transitive assembly.
------------------------------------------------------------------------

record LargeFieldAbsorptionDerivation
    (Scale Bound : Set) : Set₁ where
  field
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    zero : Bound
    multiply : Bound → Bound → Bound
    residualMagnitude residualMagnitudeSquared polynomialEnvelope : Scale → Bound
    largeFieldSuppression smallFieldScaleGain : Scale → Bound

    residualSquareDefinition : ∀ scale →
      residualMagnitudeSquared scale
      ≡ multiply (residualMagnitude scale) (residualMagnitude scale)

    residualMagnitudeSquaredBound : ∀ scale →
      LessEqual
        (residualMagnitudeSquared scale)
        (polynomialEnvelope scale)

    suppressionNonnegative : ∀ scale →
      LessEqual zero (largeFieldSuppression scale)

    multiplyRightMonotone : ∀ coefficient {left right} →
      LessEqual zero coefficient →
      LessEqual left right →
      LessEqual (multiply left coefficient) (multiply right coefficient)

    -- This is the single calculus estimate obtained from the superlinear-log
    -- p0 growth and the convention-matched running coupling.  It replaces two
    -- redundant frontier fields called "p0 dominates linear scale" and
    -- "exponential beats polynomial".
    polynomialTimesP0SuppressionGeometric : ∀ scale →
      LessEqual
        (multiply (polynomialEnvelope scale)
          (largeFieldSuppression scale))
        (smallFieldScaleGain scale)

open LargeFieldAbsorptionDerivation public

residualTimesSuppressionBelowPolynomial :
  ∀ {Scale Bound}
    (dataSet : LargeFieldAbsorptionDerivation Scale Bound)
    scale →
  LessEqual dataSet
    (multiply dataSet
      (residualMagnitudeSquared dataSet scale)
      (largeFieldSuppression dataSet scale))
    (multiply dataSet
      (polynomialEnvelope dataSet scale)
      (largeFieldSuppression dataSet scale))
residualTimesSuppressionBelowPolynomial dataSet scale =
  multiplyRightMonotone dataSet
    (largeFieldSuppression dataSet scale)
    (suppressionNonnegative dataSet scale)
    (residualMagnitudeSquaredBound dataSet scale)

largeFieldAbsorbedBySmallFieldBudget :
  ∀ {Scale Bound}
    (dataSet : LargeFieldAbsorptionDerivation Scale Bound)
    scale →
  LessEqual dataSet
    (multiply dataSet
      (residualMagnitudeSquared dataSet scale)
      (largeFieldSuppression dataSet scale))
    (smallFieldScaleGain dataSet scale)
largeFieldAbsorbedBySmallFieldBudget dataSet scale =
  transitive dataSet
    (residualTimesSuppressionBelowPolynomial dataSet scale)
    (polynomialTimesP0SuppressionGeometric dataSet scale)

record BalabanResidualEnvelope
    (Scale Bound : Set) : Set₁ where
  field
    one CResidual : Bound
    beta : Scale → Bound
    add multiply : Bound → Bound → Bound
    M : Scale → Bound
    polynomialEnvelope : Scale → Bound
    LessEqual : Bound → Bound → Set

    MDefinition : ∀ scale →
      M scale ≡ multiply CResidual (add one (beta scale))

    betaAtMostAffineInScale : ∀ scale → Set
    mSquaredAtMostPolynomialEnvelope : ∀ scale →
      LessEqual
        (multiply (M scale) (M scale))
        (polynomialEnvelope scale)

open BalabanResidualEnvelope public

p0GrowthTargetDefinitionLevel : ProofLevel
p0GrowthTargetDefinitionLevel = machineChecked

p0GrowthPrimarySourceAndRunningCouplingInputsLevel : ProofLevel
p0GrowthPrimarySourceAndRunningCouplingInputsLevel = conditional

largeFieldAbsorptionAssemblyLevel : ProofLevel
largeFieldAbsorptionAssemblyLevel = machineChecked

residualPolynomialEnvelopeInputsLevel : ProofLevel
residualPolynomialEnvelopeInputsLevel = conditional

polynomialSuppressionCalculusInputsLevel : ProofLevel
polynomialSuppressionCalculusInputsLevel = conditional
