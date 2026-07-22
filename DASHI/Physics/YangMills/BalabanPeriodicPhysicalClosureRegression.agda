module DASHI.Physics.YangMills.BalabanPeriodicPhysicalClosureRegression where

open import Agda.Builtin.Equality using (refl)

import DASHI.Physics.YangMills.BalabanPeriodicFourierHodgeRegression as Base
import DASHI.Physics.YangMills.BalabanPeriodicPhysicalConstraintMatching as Match
import DASHI.Physics.YangMills.BalabanPeriodicLocalBlockGapInhabitation as Local
import DASHI.Physics.YangMills.BalabanPeriodicFourierNormalizationMatching as Normalization
import DASHI.Physics.YangMills.BalabanPeriodicBulkHessianGreenClosure as Closure
import DASHI.Physics.YangMills.BalabanPeriodicBlockSymbolGap as Gap
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

normalizationMatch :
  Normalization.PeriodicFourierNormalizationMatch
    Base.fourierAuthority Base.fourierTheorems
normalizationMatch = record
  { Normalization.latticeSpacing = Base.one
  ; Normalization.latticeSpacingFourthPower = Base.one
  ; Normalization.siteCardinality = Base.one
  ; Normalization.inverseSiteCardinality = Base.one
  ; Normalization.physicalWeight = Base.one
  ; Normalization.multiplyAssociative = λ a b c → refl
  ; Normalization.inverseCardinalityNormalization = refl
  ; Normalization.transformNormalizationMatchesInverseCardinality = refl
  ; Normalization.transformCardinalityMatchesTorusCardinality = refl
  ; Normalization.latticeSpacingFourthPowerDefinition = refl
  ; Normalization.physicalWeightDefinition = refl
  ; Normalization.physicalBondSiteNorm = λ field → Base.one
  ; Normalization.physicalBondMomentumNorm = λ field → Base.one
  ; Normalization.physicalBondSiteNormDefinition = λ field → refl
  ; Normalization.physicalBondMomentumNormDefinition = λ field → refl
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
  { Match.GaugeOrthogonalityFourierIdentity = λ index state → Base.Holds
  ; Match.BlockAverageZeroFourierIdentity = λ index state → Base.Holds
  ; Match.ResidualGaugeOrthogonalityFourierIdentity = λ index state → Base.Holds
  ; Match.BoundaryCompatibilityFourierIdentity = λ index state → Base.Holds
  ; Match.gaugeOrthogonalityFourierIdentity =
      λ index state constraint → Base.holds
  ; Match.blockAverageZeroFourierIdentity =
      λ index state constraint → Base.holds
  ; Match.residualGaugeOrthogonalityFourierIdentity =
      λ index state constraint → Base.holds
  ; Match.boundaryCompatibilityFourierIdentity =
      λ index state constraint → Base.holds
  ; Match.ExactMode = λ index frequency → Base.Carrier.Empty
  ; Match.ResidualKernel = λ index frequency → Base.Carrier.Empty
  ; Match.BoundaryKernel = λ index frequency → Base.Carrier.Empty
  ; Match.gaugeConstraintRemovesExactModes =
      λ index state constraint impossible → impossible
  ; Match.blockConstraintRemovesConstantModes =
      λ index state constraint impossible → impossible
  ; Match.residualGaugeConstraintRemovesResidualKernel =
      λ index state constraint impossible → impossible
  ; Match.boundaryConstraintRemovesBoundaryKernel =
      λ index state constraint impossible → impossible
  ; Match.symbolKernelClassification =
      λ index frequency impossible → Base.emptyEliminate impossible
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
  { Local.cBulk = Base.one
  ; Local.cBulkPositive = Base.holds
  ; Local.Volume = Base.One
  ; Local.LatticeSpacing = Base.One
  ; Local.RGScale = Base.One
  ; Local.Background = Base.One
  ; Local.LowMomentum = λ index frequency → Base.Holds
  ; Local.HighMomentum = λ index frequency → Base.Holds
  ; Local.blockZeroModeFrequencyDecomposition =
      λ index frequency → Gap.left Base.holds
  ; Local.nonzeroMomentumDifferenceSymbolLowerBound =
      λ index frequency high → Base.holds
  ; Local.lowMomentumControlledByLocalBlockConstraint =
      λ index frequency low removed → Base.holds
  ; Local.highMomentumDifferenceEnergyBelowReference =
      λ index frequency high → Base.holds
  ; Local.GaugeLongitudinalModeControlled = λ index frequency → Base.Holds
  ; Local.TransverseModeControlledByCurl = λ index frequency → Base.Holds
  ; Local.gaugeLongitudinalModeControlled = λ index frequency → Base.holds
  ; Local.transverseModeControlledByCurl = λ index frequency → Base.holds
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
  { Closure.referenceHessian = λ index state → Base.one
  ; Closure.fullHessian = λ index state → Base.one
  ; Closure.inner = λ left right → Base.one
  ; Closure.referenceEnergyIsInner = λ index state → refl
  ; Closure.perturbationEnergy = λ index state → Base.one
  ; Closure.curvaturePart = λ index state → Base.one
  ; Closure.transportPart = λ index state → Base.one
  ; Closure.chartPart = λ index state → Base.one
  ; Closure.gaugeFixingPart = λ index state → Base.one
  ; Closure.blockConstraintPart = λ index state → Base.one
  ; Closure.curvatureUpper = Base.one
  ; Closure.transportUpper = Base.one
  ; Closure.chartUpper = Base.one
  ; Closure.gaugeFixingUpper = Base.one
  ; Closure.blockConstraintUpper = Base.one
  ; Closure.perturbationUpper = Base.one
  ; Closure.perturbationBelowFiveParts = λ index state → Base.holds
  ; Closure.curvaturePerturbationBound = λ index state → Base.holds
  ; Closure.transportPerturbationBound = λ index state → Base.holds
  ; Closure.chartPerturbationBound = λ index state → Base.holds
  ; Closure.gaugeFixingPerturbationBound = λ index state → Base.holds
  ; Closure.blockConstraintPerturbationBound = λ index state → Base.holds
  ; Closure.combineFiveScaledBounds = λ state → refl
  ; Closure.referenceBelowFullPlusPerturbation =
      λ index state tangent → Base.holds
  ; Closure.cH = Base.one
  ; Closure.cHPositive = Base.holds
  ; Closure.coercivityBudget = λ state → Base.holds
  ; Closure.reflexive = λ value → Base.holds
  ; Closure.addMonotone = λ left≤left′ right≤right′ → Base.holds
  ; Closure.addRightCancel = λ comparison → Base.holds
  ; Closure.green = λ index state → Base.one
  ; Closure.gradientGreen = λ index state → Base.one
  ; Closure.secondGradientGreen = λ index state → Base.one
  ; Closure.greenLeftInverse = λ index state → oneStateEquality state
  ; Closure.greenRightInverse = λ index state → oneStateEquality state
  ; Closure.weightedNorm = λ state → Base.one
  ; Closure.multiplyBound = Base.oneBinary
  ; Closure.reciprocalCH = Base.one
  ; Closure.CG = Base.one
  ; Closure.CGradG = Base.one
  ; Closure.CSecondGradG = Base.one
  ; Closure.reciprocalCHMatchesGreenConstant = refl
  ; Closure.bulkWeightedGreenBound = λ index source → Base.holds
  ; Closure.bulkWeightedGradientGreenBound = λ index source → Base.holds
  ; Closure.bulkWeightedSecondGradientGreenBound =
      λ index source → Base.holds
  ; Closure.greenKernel = λ index → Base.one
  ; Closure.gradientGreenKernel = λ index → Base.one
  ; Closure.secondGradientGreenKernel = λ index → Base.one
  ; Closure.KernelExponentialDecay = λ kernel → Base.Holds
  ; Closure.bulkGreenKernelExponentialDecay = λ index → Base.holds
  ; Closure.bulkGradientGreenKernelExponentialDecay = λ index → Base.holds
  ; Closure.bulkSecondGradientGreenKernelExponentialDecay =
      λ index → Base.holds
  ; Closure.BulkGreenConstantUniformInVolume = Base.Holds
  ; Closure.BulkGreenConstantUniformInSpacing = Base.Holds
  ; Closure.BulkGreenConstantUniformInScale = Base.Holds
  ; Closure.BulkGreenConstantUniformInBackground = Base.Holds
  ; Closure.bulkGreenConstantUniformInVolume = Base.holds
  ; Closure.bulkGreenConstantUniformInSpacing = Base.holds
  ; Closure.bulkGreenConstantUniformInScale = Base.holds
  ; Closure.bulkGreenConstantUniformInBackground = Base.holds
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
