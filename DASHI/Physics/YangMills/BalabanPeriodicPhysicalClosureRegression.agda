module DASHI.Physics.YangMills.BalabanPeriodicPhysicalClosureRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanPeriodicFourierHodgeRegression as Base
import DASHI.Physics.YangMills.BalabanPeriodicPhysicalConstraintMatching as Match
import DASHI.Physics.YangMills.BalabanPeriodicLocalBlockGapInhabitation as Local
import DASHI.Physics.YangMills.BalabanPeriodicFourierNormalizationMatching as Normalization
import DASHI.Physics.YangMills.BalabanPeriodicBulkHessianGreenClosure as Closure
import DASHI.Physics.YangMills.BalabanPeriodicBlockSymbolGap as Gap
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanBulkPropagatorAnalyticInhabitation as Bulk

------------------------------------------------------------------------
-- One-point regression for the exact physical adapters introduced after the
-- initial periodic Fourier tranche.  As in the earlier regression, the carrier
-- is deliberately trivial: the purpose is to exercise dependent record
-- construction, projection resolution and theorem composition, not to claim the
-- physical local-block estimate.
------------------------------------------------------------------------

oneStateEquality : ∀ state → Base.one ≡ state
oneStateEquality Base.one = refl

emptyEliminate : ∀ {A : Set} → Carrier.Empty → A
emptyEliminate ()

normalizationMatch :
  Normalization.PeriodicFourierNormalizationMatch
    Base.fourierAuthority Base.fourierTheorems
normalizationMatch = record
  { latticeSpacing = Base.one
  ; latticeSpacingFourthPower = Base.one
  ; siteCardinality = Base.one
  ; inverseSiteCardinality = Base.one
  ; physicalWeight = Base.one
  ; multiplyAssociative = λ a b c → refl
  ; inverseCardinalityNormalization = refl
  ; transformNormalizationMatchesInverseCardinality = refl
  ; transformCardinalityMatchesTorusCardinality = refl
  ; latticeSpacingFourthPowerDefinition = refl
  ; physicalWeightDefinition = refl
  ; physicalBondSiteNorm = λ field → Base.one
  ; physicalBondMomentumNorm = λ field → Base.one
  ; physicalBondSiteNormDefinition = λ field → refl
  ; physicalBondMomentumNormDefinition = λ field → refl
  }

physicalParsevalRegression : Base.one ≡ Base.one
physicalParsevalRegression =
  Normalization.physicalBondFourierParseval
    normalizationMatch Base.bondField

physicalConstraintInputs :
  Match.PhysicalConstraintFourierInputs Base.kernelData
    (λ index state → Base.Holds)
    (λ index state → Base.Holds)
    (λ index state → Base.Holds)
    (λ index state → Base.Holds)
physicalConstraintInputs = record
  { GaugeOrthogonalityFourierIdentity = λ index state → Base.Holds
  ; BlockAverageZeroFourierIdentity = λ index state → Base.Holds
  ; ResidualGaugeOrthogonalityFourierIdentity = λ index state → Base.Holds
  ; BoundaryCompatibilityFourierIdentity = λ index state → Base.Holds
  ; gaugeOrthogonalityFourierIdentity =
      λ index state constraint → Base.holds
  ; blockAverageZeroFourierIdentity =
      λ index state constraint → Base.holds
  ; residualGaugeOrthogonalityFourierIdentity =
      λ index state constraint → Base.holds
  ; boundaryCompatibilityFourierIdentity =
      λ index state constraint → Base.holds
  ; ExactMode = λ index frequency → Carrier.Empty
  ; ResidualKernel = λ index frequency → Carrier.Empty
  ; BoundaryKernel = λ index frequency → Carrier.Empty
  ; gaugeConstraintRemovesExactModes =
      λ index state constraint impossible → impossible
  ; blockConstraintRemovesConstantModes =
      λ index state constraint impossible → impossible
  ; residualGaugeConstraintRemovesResidualKernel =
      λ index state constraint impossible → impossible
  ; boundaryConstraintRemovesBoundaryKernel =
      λ index state constraint impossible → impossible
  ; symbolKernelClassification =
      λ index frequency impossible → emptyEliminate impossible
  }

matchedConstraints : Gap.PeriodicConstraintRemovalData Base.kernelData
matchedConstraints =
  Match.physicalConstraintRemovalData Base.kernelData
    (λ index state → Base.Holds)
    (λ index state → Base.Holds)
    (λ index state → Base.Holds)
    (λ index state → Base.Holds)
    physicalConstraintInputs

physicalTangent :
  Bulk.ConcreteGaugeFixedTangent
    (λ index state → Base.Holds)
    (λ index state → Base.Holds)
    (λ index state → Base.Holds)
    (λ index state → Base.Holds)
    Base.one Base.one
physicalTangent = Bulk.gaugeFixedTangent
  Base.holds Base.holds Base.holds Base.holds

physicalKernelRemovalRegression :
  Gap.SymbolKernelRemoved matchedConstraints Base.one Base.one
physicalKernelRemovalRegression =
  Match.physicalGaugeFixedTangentRemovesReferenceKernel Base.kernelData
    (λ index state → Base.Holds)
    (λ index state → Base.Holds)
    (λ index state → Base.Holds)
    (λ index state → Base.Holds)
    physicalConstraintInputs Base.one Base.one physicalTangent

localGapInputs : Local.PhysicalLocalBlockGapInputs matchedConstraints
localGapInputs = record
  { cBulk = Base.one
  ; cBulkPositive = Base.holds
  ; Volume = Base.One
  ; LatticeSpacing = Base.One
  ; RGScale = Base.One
  ; Background = Base.One
  ; LowMomentum = λ index frequency → Base.Holds
  ; HighMomentum = λ index frequency → Base.Holds
  ; blockZeroModeFrequencyDecomposition =
      λ index frequency → Gap.left Base.holds
  ; nonzeroMomentumDifferenceSymbolLowerBound =
      λ index frequency high → Base.holds
  ; lowMomentumControlledByLocalBlockConstraint =
      λ index frequency low removed → Base.holds
  ; highMomentumDifferenceEnergyBelowReference =
      λ index frequency high → Base.holds
  ; GaugeLongitudinalModeControlled = λ index frequency → Base.Holds
  ; TransverseModeControlledByCurl = λ index frequency → Base.Holds
  ; gaugeLongitudinalModeControlled = λ index frequency → Base.holds
  ; transverseModeControlledByCurl = λ index frequency → Base.holds
  }

localGapRegression : Base.Holds
localGapRegression =
  Local.physicalLocalBlockGapImpliesUniformReferenceGap
    localGapInputs Base.one Base.one physicalKernelRemovalRegression

bulkInputs :
  Closure.PeriodicBulkHessianGreenInputs
    {symbolData = Base.symbolData}
    {kernelData = Base.kernelData}
    {constraints = matchedConstraints}
    {Kernel = Base.One}
    localGapInputs
bulkInputs = record
  { referenceHessian = λ index state → Base.one
  ; fullHessian = λ index state → Base.one
  ; inner = λ left right → Base.one
  ; referenceEnergyIsInner = λ index state → refl
  ; perturbationEnergy = λ index state → Base.one
  ; curvaturePart = λ index state → Base.one
  ; transportPart = λ index state → Base.one
  ; chartPart = λ index state → Base.one
  ; gaugeFixingPart = λ index state → Base.one
  ; blockConstraintPart = λ index state → Base.one
  ; curvatureUpper = Base.one
  ; transportUpper = Base.one
  ; chartUpper = Base.one
  ; gaugeFixingUpper = Base.one
  ; blockConstraintUpper = Base.one
  ; perturbationUpper = Base.one
  ; perturbationBelowFiveParts = λ index state → Base.holds
  ; curvaturePerturbationBound = λ index state → Base.holds
  ; transportPerturbationBound = λ index state → Base.holds
  ; chartPerturbationBound = λ index state → Base.holds
  ; gaugeFixingPerturbationBound = λ index state → Base.holds
  ; blockConstraintPerturbationBound = λ index state → Base.holds
  ; combineFiveScaledBounds = λ state → refl
  ; referenceBelowFullPlusPerturbation =
      λ index state tangent → Base.holds
  ; cH = Base.one
  ; cHPositive = Base.holds
  ; coercivityBudget = λ state → Base.holds
  ; reflexive = λ value → Base.holds
  ; addMonotone = λ left≤left′ right≤right′ → Base.holds
  ; addRightCancel = λ comparison → Base.holds
  ; green = λ index state → Base.one
  ; gradientGreen = λ index state → Base.one
  ; secondGradientGreen = λ index state → Base.one
  ; greenLeftInverse = λ index state → oneStateEquality state
  ; greenRightInverse = λ index state → oneStateEquality state
  ; weightedNorm = λ state → Base.one
  ; multiplyBound = Base.oneBinary
  ; reciprocalCH = Base.one
  ; CG = Base.one
  ; CGradG = Base.one
  ; CSecondGradG = Base.one
  ; reciprocalCHMatchesGreenConstant = refl
  ; bulkWeightedGreenBound = λ index source → Base.holds
  ; bulkWeightedGradientGreenBound = λ index source → Base.holds
  ; bulkWeightedSecondGradientGreenBound =
      λ index source → Base.holds
  ; greenKernel = λ index → Base.one
  ; gradientGreenKernel = λ index → Base.one
  ; secondGradientGreenKernel = λ index → Base.one
  ; KernelExponentialDecay = λ kernel → Base.Holds
  ; bulkGreenKernelExponentialDecay = λ index → Base.holds
  ; bulkGradientGreenKernelExponentialDecay = λ index → Base.holds
  ; bulkSecondGradientGreenKernelExponentialDecay =
      λ index → Base.holds
  ; BulkGreenConstantUniformInVolume = Base.Holds
  ; BulkGreenConstantUniformInSpacing = Base.Holds
  ; BulkGreenConstantUniformInScale = Base.Holds
  ; BulkGreenConstantUniformInBackground = Base.Holds
  ; bulkGreenConstantUniformInVolume = Base.holds
  ; bulkGreenConstantUniformInSpacing = Base.holds
  ; bulkGreenConstantUniformInScale = Base.holds
  ; bulkGreenConstantUniformInBackground = Base.holds
  }

fullHessianCoercivityRegression : Base.Holds
fullHessianCoercivityRegression =
  Closure.uniformConstrainedHessianCoercive
    bulkInputs Base.one Base.one physicalTangent

bulkGreenCertificate :
  Closure.PeriodicBulkHessianGreenCertificate
    Base.One Base.One Base.One Base.One
bulkGreenCertificate =
  Closure.periodicBulkHessianGreenCertificate bulkInputs
