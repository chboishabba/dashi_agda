module DASHI.Physics.YangMills.BalabanBulkPropagatorAnalyticInhabitation where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Concrete finite-background ownership.
------------------------------------------------------------------------

record ConcreteBalabanIndex
    (Lattice Spacing Scale Background Patch Domain Radius : Set) : Set where
  constructor finiteBackgroundIndex
  field
    Λ : Lattice
    a : Spacing
    k : Scale
    U₀ : Background
    P : Patch
    Ω : Domain
    r : Radius
open ConcreteBalabanIndex public

record ConcreteGaugeFixedTangent
    {Index State : Set}
    (GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
      BoundaryCompatible : Index → State → Set)
    (index : Index) (state : State) : Set where
  constructor gaugeFixedTangent
  field
    gaugeOrthogonal : GaugeOrthogonal index state
    blockAverageZero : BlockAverageZero index state
    residualGaugeOrthogonal : ResidualGaugeOrthogonal index state
    boundaryCompatible : BoundaryCompatible index state
open ConcreteGaugeFixedTangent public

ConcreteReferenceEnergy : Set → Set → Set → Set
ConcreteReferenceEnergy Index State Bound = Index → State → Bound

ConcreteBulkHessian : Set → Set → Set
ConcreteBulkHessian Index State = Index → State → State

ConcreteWeightedNorm : Set → Set → Set
ConcreteWeightedNorm State Bound = State → Bound

ConcreteBulkGreen ConcreteBulkGradientGreen ConcreteBulkSecondGradientGreen :
  Set → Set → Set
ConcreteBulkGreen Index State = Index → State → State
ConcreteBulkGradientGreen Index State = Index → State → State
ConcreteBulkSecondGradientGreen Index State = Index → State → State

------------------------------------------------------------------------
-- One coherent proof-relevant owner for the complete bulk/patch/residual/
-- nonlinear analytic cutset.  Every proposition has an inhabitant field; no
-- String evidence, Boolean proxy or local postulate is used.
------------------------------------------------------------------------

record BulkPropagatorAnalyticInputs : Set₁ where
  field
    -- Concrete operator ownership and exact identities.
    BulkHessianIsReferenceEnergyOperator : Set
    bulkHessianIsReferenceEnergyOperator :
      BulkHessianIsReferenceEnergyOperator
    BulkHessianPreservesGaugeFixedTangent : Set
    bulkHessianPreservesGaugeFixedTangent :
      BulkHessianPreservesGaugeFixedTangent
    BulkHessianSelfAdjoint : Set
    bulkHessianSelfAdjoint : BulkHessianSelfAdjoint
    BulkHessianPositiveSemidefinite : Set
    bulkHessianPositiveSemidefinite : BulkHessianPositiveSemidefinite
    BulkGreenLeftInverse : Set
    bulkGreenLeftInverse : BulkGreenLeftInverse
    BulkGreenRightInverse : Set
    bulkGreenRightInverse : BulkGreenRightInverse

    -- Exact discrete Hodge identity and zero modes.
    BulkCovariantHodgeIdentity : Set
    bulkCovariantHodgeIdentity : BulkCovariantHodgeIdentity
    BulkGaugeFixingTermIdentity : Set
    bulkGaugeFixingTermIdentity : BulkGaugeFixingTermIdentity
    BulkBlockConstraintTermIdentity : Set
    bulkBlockConstraintTermIdentity : BulkBlockConstraintTermIdentity
    BulkCurvatureRemainderIdentity : Set
    bulkCurvatureRemainderIdentity : BulkCurvatureRemainderIdentity
    GaugeExactModesRemoved : Set
    gaugeExactModesRemoved : GaugeExactModesRemoved
    BlockConstantModesRemoved : Set
    blockConstantModesRemoved : BlockConstantModesRemoved
    ResidualGaugeModesRemoved : Set
    residualGaugeModesRemoved : ResidualGaugeModesRemoved
    ConstraintKernelTrivial : Set
    constraintKernelTrivial : ConstraintKernelTrivial
    ReferenceEnergyZeroImpliesZero : Set
    referenceEnergyZeroImpliesZero : ReferenceEnergyZeroImpliesZero

    -- Poincare and uniform Hodge coercivity.
    PeriodicScalarPoincare : Set
    periodicScalarPoincare : PeriodicScalarPoincare
    PeriodicBondPoincare : Set
    periodicBondPoincare : PeriodicBondPoincare
    BlockZeroPoincare : Set
    blockZeroPoincare : BlockZeroPoincare
    CovariantPoincareSmallCurvature : Set
    covariantPoincareSmallCurvature : CovariantPoincareSmallCurvature
    BulkGaugeFixedHodgePoincare : Set
    bulkGaugeFixedHodgePoincare : BulkGaugeFixedHodgePoincare
    CBulkPositive : Set
    cBulkPositive : CBulkPositive
    CBulkIndependentOfVolume : Set
    cBulkIndependentOfVolume : CBulkIndependentOfVolume
    CBulkIndependentOfLatticeSpacing : Set
    cBulkIndependentOfLatticeSpacing : CBulkIndependentOfLatticeSpacing
    CBulkIndependentOfScale : Set
    cBulkIndependentOfScale : CBulkIndependentOfScale
    CBulkUniformOverAdmissibleBackgrounds : Set
    cBulkUniformOverAdmissibleBackgrounds :
      CBulkUniformOverAdmissibleBackgrounds

    -- Exact Hessian difference and perturbation budget.
    FullHessianDifferenceExact : Set
    fullHessianDifferenceExact : FullHessianDifferenceExact
    CurvaturePerturbationExact : Set
    curvaturePerturbationExact : CurvaturePerturbationExact
    TransportPerturbationExact : Set
    transportPerturbationExact : TransportPerturbationExact
    ChartPerturbationExact : Set
    chartPerturbationExact : ChartPerturbationExact
    GaugeFixingPerturbationExact : Set
    gaugeFixingPerturbationExact : GaugeFixingPerturbationExact
    BlockConstraintPerturbationExact : Set
    blockConstraintPerturbationExact : BlockConstraintPerturbationExact
    CurvatureHessianPerturbationBound : Set
    curvatureHessianPerturbationBound : CurvatureHessianPerturbationBound
    TransportHessianPerturbationBound : Set
    transportHessianPerturbationBound : TransportHessianPerturbationBound
    ChartHessianPerturbationBound : Set
    chartHessianPerturbationBound : ChartHessianPerturbationBound
    GaugeFixingHessianPerturbationBound : Set
    gaugeFixingHessianPerturbationBound : GaugeFixingHessianPerturbationBound
    BlockConstraintHessianPerturbationBound : Set
    blockConstraintHessianPerturbationBound :
      BlockConstraintHessianPerturbationBound
    TotalHessianPerturbationBound : Set
    totalHessianPerturbationBound : TotalHessianPerturbationBound
    δTotalMonotone : Set
    δTotalIsMonotone : δTotalMonotone
    δTotalTendsToZero : Set
    δTotalVanishes : δTotalTendsToZero
    ChooseRadiusWithδTotalBelowBulkGap : Set
    chooseRadiusWithδTotalBelowBulkGap :
      ChooseRadiusWithδTotalBelowBulkGap
    UniformConstrainedHessianCoercive : Set
    uniformConstrainedHessianCoercive : UniformConstrainedHessianCoercive

    -- Bulk Green kernel and weighted Schur estimates.
    BulkGreenKernelExists : Set
    bulkGreenKernelExists : BulkGreenKernelExists
    BulkGreenKernelRepresentsInverse : Set
    bulkGreenKernelRepresentsInverse : BulkGreenKernelRepresentsInverse
    BulkGreenKernelGaugeCovariant : Set
    bulkGreenKernelGaugeCovariant : BulkGreenKernelGaugeCovariant
    BulkGreenKernelAdjointSymmetry : Set
    bulkGreenKernelAdjointSymmetry : BulkGreenKernelAdjointSymmetry
    BulkGreenNearDiagonalBound : Set
    bulkGreenNearDiagonalBound : BulkGreenNearDiagonalBound
    BulkGreenOffDiagonalDecay : Set
    bulkGreenOffDiagonalDecay : BulkGreenOffDiagonalDecay
    BulkGreenKernelExponentialDecay : Set
    bulkGreenKernelExponentialDecay : BulkGreenKernelExponentialDecay
    BulkGradientGreenKernelIdentity : Set
    bulkGradientGreenKernelIdentity : BulkGradientGreenKernelIdentity
    BulkGradientGreenNearDiagonalBound : Set
    bulkGradientGreenNearDiagonalBound : BulkGradientGreenNearDiagonalBound
    BulkGradientGreenExponentialDecay : Set
    bulkGradientGreenExponentialDecay : BulkGradientGreenExponentialDecay
    BulkSecondGradientGreenKernelIdentity : Set
    bulkSecondGradientGreenKernelIdentity : BulkSecondGradientGreenKernelIdentity
    BulkSecondGradientGreenNearDiagonalBound : Set
    bulkSecondGradientGreenNearDiagonalBound :
      BulkSecondGradientGreenNearDiagonalBound
    BulkSecondGradientGreenExponentialDecay : Set
    bulkSecondGradientGreenExponentialDecay :
      BulkSecondGradientGreenExponentialDecay
    BulkGreenWeightedRowSum : Set
    bulkGreenWeightedRowSum : BulkGreenWeightedRowSum
    BulkGreenWeightedColumnSum : Set
    bulkGreenWeightedColumnSum : BulkGreenWeightedColumnSum
    BulkGradientGreenWeightedRowSum : Set
    bulkGradientGreenWeightedRowSum : BulkGradientGreenWeightedRowSum
    BulkGradientGreenWeightedColumnSum : Set
    bulkGradientGreenWeightedColumnSum : BulkGradientGreenWeightedColumnSum
    BulkSecondGradientGreenWeightedRowSum : Set
    bulkSecondGradientGreenWeightedRowSum :
      BulkSecondGradientGreenWeightedRowSum
    BulkSecondGradientGreenWeightedColumnSum : Set
    bulkSecondGradientGreenWeightedColumnSum :
      BulkSecondGradientGreenWeightedColumnSum
    BulkWeightedGreenBound : Set
    bulkWeightedGreenBound : BulkWeightedGreenBound
    BulkWeightedGradientGreenBound : Set
    bulkWeightedGradientGreenBound : BulkWeightedGradientGreenBound
    BulkWeightedSecondGradientGreenBound : Set
    bulkWeightedSecondGradientGreenBound : BulkWeightedSecondGradientGreenBound
    BulkGreenConstantUniformInVolume : Set
    bulkGreenConstantUniformInVolume : BulkGreenConstantUniformInVolume
    BulkGreenConstantUniformInSpacing : Set
    bulkGreenConstantUniformInSpacing : BulkGreenConstantUniformInSpacing
    BulkGreenConstantUniformInScale : Set
    bulkGreenConstantUniformInScale : BulkGreenConstantUniformInScale
    BulkGreenConstantUniformInBackground : Set
    bulkGreenConstantUniformInBackground : BulkGreenConstantUniformInBackground
    BulkGradientConstantUniform : Set
    bulkGradientConstantUniform : BulkGradientConstantUniform
    BulkSecondGradientConstantUniform : Set
    bulkSecondGradientConstantUniform : BulkSecondGradientConstantUniform

    -- Concrete boundary/interface/corner/nested geometry.
    ConcreteBoundaryExtension : Set
    concreteBoundaryExtension : ConcreteBoundaryExtension
    ConcreteBoundaryRestriction : Set
    concreteBoundaryRestriction : ConcreteBoundaryRestriction
    BoundaryRestrictionExtensionRetract : Set
    boundaryRestrictionExtensionRetract : BoundaryRestrictionExtensionRetract
    BoundaryExtensionPreservesGaugeConstraint : Set
    boundaryExtensionPreservesGaugeConstraint :
      BoundaryExtensionPreservesGaugeConstraint
    BoundaryExtensionPreservesBlockConstraint : Set
    boundaryExtensionPreservesBlockConstraint :
      BoundaryExtensionPreservesBlockConstraint
    BoundaryExtensionWeightedNormBound : Set
    boundaryExtensionWeightedNormBound : BoundaryExtensionWeightedNormBound
    BoundaryRestrictionWeightedNormBound : Set
    boundaryRestrictionWeightedNormBound : BoundaryRestrictionWeightedNormBound
    BoundaryEnergyComparedToBulk : Set
    boundaryEnergyComparedToBulk : BoundaryEnergyComparedToBulk

    ConcreteInterfaceExtension : Set
    concreteInterfaceExtension : ConcreteInterfaceExtension
    ConcreteInterfaceRestriction : Set
    concreteInterfaceRestriction : ConcreteInterfaceRestriction
    InterfaceRestrictionExtensionRetract : Set
    interfaceRestrictionExtensionRetract : InterfaceRestrictionExtensionRetract
    InterfaceExtensionPreservesConstraints : Set
    interfaceExtensionPreservesConstraints : InterfaceExtensionPreservesConstraints
    InterfaceExtensionWeightedNormBound : Set
    interfaceExtensionWeightedNormBound : InterfaceExtensionWeightedNormBound
    InterfaceRestrictionWeightedNormBound : Set
    interfaceRestrictionWeightedNormBound : InterfaceRestrictionWeightedNormBound
    InterfaceEnergyComparedToBulk : Set
    interfaceEnergyComparedToBulk : InterfaceEnergyComparedToBulk

    ConcreteCornerExtension : Set
    concreteCornerExtension : ConcreteCornerExtension
    ConcreteCornerRestriction : Set
    concreteCornerRestriction : ConcreteCornerRestriction
    CornerRestrictionExtensionRetract : Set
    cornerRestrictionExtensionRetract : CornerRestrictionExtensionRetract
    CornerExtensionPreservesConstraints : Set
    cornerExtensionPreservesConstraints : CornerExtensionPreservesConstraints
    CornerExtensionWeightedNormBound : Set
    cornerExtensionWeightedNormBound : CornerExtensionWeightedNormBound
    CornerRestrictionWeightedNormBound : Set
    cornerRestrictionWeightedNormBound : CornerRestrictionWeightedNormBound
    CornerEnergyComparedToBulk : Set
    cornerEnergyComparedToBulk : CornerEnergyComparedToBulk

    ConcreteNestedExtension : Set
    concreteNestedExtension : ConcreteNestedExtension
    ConcreteNestedRestriction : Set
    concreteNestedRestriction : ConcreteNestedRestriction
    NestedRestrictionExtensionRetract : Set
    nestedRestrictionExtensionRetract : NestedRestrictionExtensionRetract
    NestedExtensionPreservesConstraints : Set
    nestedExtensionPreservesConstraints : NestedExtensionPreservesConstraints
    NestedExtensionWeightedNormBound : Set
    nestedExtensionWeightedNormBound : NestedExtensionWeightedNormBound
    NestedRestrictionWeightedNormBound : Set
    nestedRestrictionWeightedNormBound : NestedRestrictionWeightedNormBound
    NestedEnergyComparedToBulk : Set
    nestedEnergyComparedToBulk : NestedEnergyComparedToBulk

    BoundaryGreenIntertwining InterfaceGreenIntertwining
      CornerGreenIntertwining NestedGreenIntertwining : Set
    boundaryGreenIntertwining : BoundaryGreenIntertwining
    interfaceGreenIntertwining : InterfaceGreenIntertwining
    cornerGreenIntertwining : CornerGreenIntertwining
    nestedGreenIntertwining : NestedGreenIntertwining
    BoundaryGradientGreenIntertwining InterfaceGradientGreenIntertwining
      CornerGradientGreenIntertwining NestedGradientGreenIntertwining : Set
    boundaryGradientGreenIntertwining : BoundaryGradientGreenIntertwining
    interfaceGradientGreenIntertwining : InterfaceGradientGreenIntertwining
    cornerGradientGreenIntertwining : CornerGradientGreenIntertwining
    nestedGradientGreenIntertwining : NestedGradientGreenIntertwining
    BoundarySecondGradientGreenIntertwining
      InterfaceSecondGradientGreenIntertwining
      CornerSecondGradientGreenIntertwining
      NestedSecondGradientGreenIntertwining : Set
    boundarySecondGradientGreenIntertwining :
      BoundarySecondGradientGreenIntertwining
    interfaceSecondGradientGreenIntertwining :
      InterfaceSecondGradientGreenIntertwining
    cornerSecondGradientGreenIntertwining :
      CornerSecondGradientGreenIntertwining
    nestedSecondGradientGreenIntertwining :
      NestedSecondGradientGreenIntertwining
    BoundaryGreenCorrectionBound InterfaceGreenCorrectionBound
      CornerGreenCorrectionBound NestedGreenCorrectionBound : Set
    boundaryGreenCorrectionBound : BoundaryGreenCorrectionBound
    interfaceGreenCorrectionBound : InterfaceGreenCorrectionBound
    cornerGreenCorrectionBound : CornerGreenCorrectionBound
    nestedGreenCorrectionBound : NestedGreenCorrectionBound

    -- Local parametrix and strict residual.
    LocalPartitionOfUnity LocalPartitionFiniteOverlap
      LocalPartitionGradientBound LocalPartitionSecondGradientBound
      SupportContainedInEnlargedPatch : Set
    localPartitionOfUnity : LocalPartitionOfUnity
    localPartitionFiniteOverlap : LocalPartitionFiniteOverlap
    localPartitionGradientBound : LocalPartitionGradientBound
    localPartitionSecondGradientBound : LocalPartitionSecondGradientBound
    supportContainedInEnlargedPatch : SupportContainedInEnlargedPatch
    LocalHessianInverseExists LocalGreenWeightedBound
      LocalGradientGreenWeightedBound LocalSecondGradientGreenWeightedBound : Set
    localHessianInverseExists : LocalHessianInverseExists
    localGreenWeightedBound : LocalGreenWeightedBound
    localGradientGreenWeightedBound : LocalGradientGreenWeightedBound
    localSecondGradientGreenWeightedBound : LocalSecondGradientGreenWeightedBound
    LocalParametrixDefinition LocalParametrixResidualEquation : Set
    localParametrixDefinition : LocalParametrixDefinition
    localParametrixResidualEquation : LocalParametrixResidualEquation
    ResidualDecomposes ResidualLocalizationCommutatorPart ResidualOverlapPart
      ResidualBoundaryPart ResidualInterfacePart ResidualCornerPart
      ResidualNestedPart ResidualBackgroundPart : Set
    residualDecomposes : ResidualDecomposes
    residualLocalizationCommutatorPart : ResidualLocalizationCommutatorPart
    residualOverlapPart : ResidualOverlapPart
    residualBoundaryPart : ResidualBoundaryPart
    residualInterfacePart : ResidualInterfacePart
    residualCornerPart : ResidualCornerPart
    residualNestedPart : ResidualNestedPart
    residualBackgroundPart : ResidualBackgroundPart
    LocalizationCommutatorResidualBound OverlapResidualBound
      BoundaryResidualBound InterfaceResidualBound CornerResidualBound
      NestedResidualBound BackgroundResidualBound : Set
    localizationCommutatorResidualBound : LocalizationCommutatorResidualBound
    overlapResidualBound : OverlapResidualBound
    boundaryResidualBound : BoundaryResidualBound
    interfaceResidualBound : InterfaceResidualBound
    cornerResidualBound : CornerResidualBound
    nestedResidualBound : NestedResidualBound
    backgroundResidualBound : BackgroundResidualBound
    BulkWeightedResidualBound PatchResidualControlledByBulk
      EachResidualBelowCommon QCommonPositive QCommonStrict : Set
    bulkWeightedResidualBound : BulkWeightedResidualBound
    patchResidualControlledByBulk : PatchResidualControlledByBulk
    eachResidualBelowCommon : EachResidualBelowCommon
    qCommonPositive : QCommonPositive
    qCommonStrict : QCommonStrict
    ResidualPowerBound GeometricResidualTailBound NeumannSeriesConverges
      CorrectionInverseExists UniformCorrectionInverseBound
      FullGreenFactorization UniformWeightedGreenBound
      UniformWeightedGradientGreenBound
      UniformWeightedSecondGradientGreenBound : Set
    residualPowerBound : ResidualPowerBound
    geometricResidualTailBound : GeometricResidualTailBound
    neumannSeriesConverges : NeumannSeriesConverges
    correctionInverseExists : CorrectionInverseExists
    uniformCorrectionInverseBound : UniformCorrectionInverseBound
    fullGreenFactorization : FullGreenFactorization
    uniformWeightedGreenBound : UniformWeightedGreenBound
    uniformWeightedGradientGreenBound : UniformWeightedGradientGreenBound
    uniformWeightedSecondGradientGreenBound :
      UniformWeightedSecondGradientGreenBound

    -- Seven nonlinear mechanisms and common Lipschitz constant.
    CompactLieBracketInequality BCHThirdOrderRemainderBound
      BCHDerivativeDifferenceBound BCHHigherLipschitz : Set
    compactLieBracketInequality : CompactLieBracketInequality
    bchThirdOrderRemainderBound : BCHThirdOrderRemainderBound
    bchDerivativeDifferenceBound : BCHDerivativeDifferenceBound
    bchHigherLipschitz : BCHHigherLipschitz
    CommutatorRemainderExact CommutatorRemainderLipschitz : Set
    commutatorRemainderExact : CommutatorRemainderExact
    commutatorRemainderLipschitz : CommutatorRemainderLipschitz
    ParallelTransportDifferenceExact ParallelTransportRemainderLipschitz : Set
    parallelTransportDifferenceExact : ParallelTransportDifferenceExact
    parallelTransportRemainderLipschitz : ParallelTransportRemainderLipschitz
    BackgroundDerivativeDifferenceExact
      BackgroundDerivativeRemainderLipschitz : Set
    backgroundDerivativeDifferenceExact : BackgroundDerivativeDifferenceExact
    backgroundDerivativeRemainderLipschitz :
      BackgroundDerivativeRemainderLipschitz
    GaugeFixingNonlinearDifferenceExact GaugeFixingRemainderLipschitz : Set
    gaugeFixingNonlinearDifferenceExact : GaugeFixingNonlinearDifferenceExact
    gaugeFixingRemainderLipschitz : GaugeFixingRemainderLipschitz
    BlockConstraintNonlinearDifferenceExact
      BlockConstraintRemainderLipschitz : Set
    blockConstraintNonlinearDifferenceExact :
      BlockConstraintNonlinearDifferenceExact
    blockConstraintRemainderLipschitz : BlockConstraintRemainderLipschitz
    ChartChangeDifferenceExact ChartChangeRemainderLipschitz : Set
    chartChangeDifferenceExact : ChartChangeDifferenceExact
    chartChangeRemainderLipschitz : ChartChangeRemainderLipschitz
    NonlinearDifferenceExactSevenPartDecomposition
      SevenComponentConstantBound UniformNonlinearRemainderLipschitz
      LNMonotone LNTendsToZero : Set
    nonlinearDifferenceExactSevenPartDecomposition :
      NonlinearDifferenceExactSevenPartDecomposition
    sevenComponentConstantBound : SevenComponentConstantBound
    uniformNonlinearRemainderLipschitz : UniformNonlinearRemainderLipschitz
    LNIsMonotone : LNMonotone
    LNVanishes : LNTendsToZero

open BulkPropagatorAnalyticInputs public

bulkPropagatorAnalyticAssemblyLevel : ProofLevel
bulkPropagatorAnalyticAssemblyLevel = machineChecked

bulkPropagatorAnalyticInputLevel : ProofLevel
bulkPropagatorAnalyticInputLevel = conditional
