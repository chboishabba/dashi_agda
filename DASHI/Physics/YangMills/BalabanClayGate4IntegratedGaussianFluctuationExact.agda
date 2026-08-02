module DASHI.Physics.YangMills.BalabanClayGate4IntegratedGaussianFluctuationExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Integrated, rather than pointwise, fluctuation control.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization II: Localization, Exponentiation, and Bounds
-- for the R-Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- The localized bilinear fluctuation factor is generally not uniformly small
-- pointwise in the fluctuation field.  The valid estimate is obtained after
-- integrating against the conditioned Gaussian and completing the square.
-- Consequently this interface intentionally contains no pointwise-bound field.
------------------------------------------------------------------------

record FluctuationOrderAlgebra (Bound : Set) : Set₁ where
  field
    multiply : Bound → Bound → Bound
    LessEqual StrictlyLess : Bound → Bound → Set
    half : Bound

open FluctuationOrderAlgebra public

record IntegratedGaussianFluctuation
    (Fluctuation LocalFactor IntegratedValue Bound : Set)
    (algebra : FluctuationOrderAlgebra Bound) : Set₁ where
  field
    covarianceNorm alpha5 : Bound

    shiftedGaussianSmallness :
      StrictlyLess algebra
        (multiply algebra alpha5 covarianceNorm)
        (half algebra)

    localFactor : LocalFactor
    integrateAgainstConditionedGaussian :
      LocalFactor → IntegratedValue

    integratedMajorant : Bound
    IntegratedAbsoluteValueBelow : IntegratedValue → Bound → Set

    integratedLocalMajorant :
      IntegratedAbsoluteValueBelow
        (integrateAgainstConditionedGaussian localFactor)
        integratedMajorant

open IntegratedGaussianFluctuation public

integratedFluctuationBound :
  ∀ {Fluctuation LocalFactor IntegratedValue Bound}
    {algebra : FluctuationOrderAlgebra Bound} →
  (dataSet : IntegratedGaussianFluctuation
    Fluctuation LocalFactor IntegratedValue Bound algebra) →
  IntegratedAbsoluteValueBelow dataSet
    (integrateAgainstConditionedGaussian dataSet (localFactor dataSet))
    (integratedMajorant dataSet)
integratedFluctuationBound dataSet = integratedLocalMajorant dataSet

record GaussianCompletionCertificate
    (Fluctuation LocalFactor IntegratedValue Bound : Set)
    (algebra : FluctuationOrderAlgebra Bound) : Set₁ where
  field
    fluctuationData : IntegratedGaussianFluctuation
      Fluctuation LocalFactor IntegratedValue Bound algebra

    shiftedQuadraticForm : Fluctuation → Bound
    linearSource : Fluctuation → Bound
    completedSquare : Fluctuation → Bound
    normalizationCorrection : Bound

    completionIdentity : ∀ fluctuation →
      multiply algebra
        (shiftedQuadraticForm fluctuation)
        (linearSource fluctuation)
      ≡ multiply algebra
          (completedSquare fluctuation)
          normalizationCorrection

    completionControlsIntegratedMajorant : Set
    completionControlsIntegratedMajorantEvidence :
      completionControlsIntegratedMajorant

open GaussianCompletionCertificate public

record ScaleUniformIntegratedFluctuation
    (Scale Fluctuation LocalFactor IntegratedValue Bound : Set)
    (algebra : FluctuationOrderAlgebra Bound) : Set₁ where
  field
    atScale : Scale → IntegratedGaussianFluctuation
      Fluctuation LocalFactor IntegratedValue Bound algebra
    uniformMajorant : Bound
    majorantAtScaleBelowUniform : ∀ scale →
      LessEqual algebra
        (integratedMajorant (atScale scale))
        uniformMajorant

open ScaleUniformIntegratedFluctuation public

integratedGaussianConsumerLevel : ProofLevel
integratedGaussianConsumerLevel = machineChecked

pointwiseFluctuationBoundNotRequiredLevel : ProofLevel
pointwiseFluctuationBoundNotRequiredLevel = machineChecked

physicalCovarianceSmallnessInputsLevel : ProofLevel
physicalCovarianceSmallnessInputsLevel = conditional

physicalGaussianCompletionInputsLevel : ProofLevel
physicalGaussianCompletionInputsLevel = conditional

physicalIntegratedFluctuationMajorantInputsLevel : ProofLevel
physicalIntegratedFluctuationMajorantInputsLevel = conditional
