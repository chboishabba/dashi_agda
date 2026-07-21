module DASHI.Physics.YangMills.BalabanBulkPropagatorAnalyticInhabitation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    first : A
    second : B
open _×_ public

------------------------------------------------------------------------
-- Concrete finite-background index and constrained tangent carrier.
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
-- Bulk Hodge, zero-mode, Poincare and Hessian perturbation inputs.
------------------------------------------------------------------------

record BulkHodgeAnalyticInputs
    (Index State ScalarState Bound Radius : Set) : Set₁ where
  field
    zeroState : State
    zeroBound : Bound
    add multiply : Bound → Bound → Bound
    LessEqual StrictLess : Bound → Bound → Set
    transitive : ∀ {a b c} → LessEqual a b → LessEqual b c → LessEqual a c

    inner : State → State → Bound
    normSq : State → Bound
    referenceEnergy : ConcreteReferenceEnergy Index State Bound
    bulkHessian fullHessian : ConcreteBulkHessian Index State

    GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
      BoundaryCompatible : Index → State → Set
    GaugeFixed : Index → State → Set
    gaugeFixedStructure : ∀ index state → GaugeFixed index state →
      ConcreteGaugeFixedTangent GaugeOrthogonal BlockAverageZero
        ResidualGaugeOrthogonal BoundaryCompatible index state

    dCovariant dCovariantAdjoint blockProjection : Index → State → State
    curvatureRemainder : Index → State → Bound

    bulkHessianIsReferenceEnergyOperatorInput : ∀ index state →
      referenceEnergy index state ≡ inner state (bulkHessian index state)
    bulkHessianPreservesGaugeFixedTangentInput : ∀ index state →
      GaugeFixed index state → GaugeFixed index (bulkHessian index state)

    SelfAdjoint PositiveSemidefinite : ConcreteBulkHessian Index State → Set
    bulkHessianSelfAdjointInput : SelfAdjoint bulkHessian
    bulkHessianPositiveSemidefiniteInput : PositiveSemidefinite bulkHessian

    bulkCovariantHodgeIdentityInput : ∀ index state →
      referenceEnergy index state ≡
      add (normSq (dCovariant index state))
        (add (normSq (dCovariantAdjoint index state))
          (add (normSq (blockProjection index state))
            (curvatureRemainder index state)))

    BulkGaugeFixingTermIdentity BulkBlockConstraintTermIdentity
      BulkCurvatureRemainderIdentity : Set
    bulkGaugeFixingTermIdentityInput : BulkGaugeFixingTermIdentity
    bulkBlockConstraintTermIdentityInput : BulkBlockConstraintTermIdentity
    bulkCurvatureRemainderIdentityInput : BulkCurvatureRemainderIdentity

    GaugeExactModesRemoved BlockConstantModesRemoved ResidualGaugeModesRemoved
      ConstraintKernelTrivial : Set
    gaugeExactModesRemovedInput : GaugeExactModesRemoved
    blockConstantModesRemovedInput : BlockConstantModesRemoved
    residualGaugeModesRemovedInput : ResidualGaugeModesRemoved
    constraintKernelTrivialInput : ConstraintKernelTrivial

    referenceEnergyZeroImpliesZeroInput : ∀ index state →
      GaugeFixed index state → referenceEnergy index state ≡ zeroBound →
      state ≡ zeroState

    PeriodicScalarPoincare PeriodicBondPoincare BlockZeroPoincare
      CovariantPoincareSmallCurvature : Set
    periodicScalarPoincareInput : PeriodicScalarPoincare
    periodicBondPoincareInput : PeriodicBondPoincare
    blockZeroPoincareInput : BlockZeroPoincare
    covariantPoincareSmallCurvatureInput : CovariantPoincareSmallCurvature

    cBulk : Bound
    Positive : Bound → Set
    cBulkPositiveInput : Positive cBulk
    bulkGaugeFixedHodgePoincareInput : ∀ index state →
      GaugeFixed index state →
      LessEqual (multiply cBulk (normSq state)) (referenceEnergy index state)

    CBulkIndependentOfVolume CBulkIndependentOfLatticeSpacing
      CBulkIndependentOfScale CBulkUniformOverAdmissibleBackgrounds : Set
    cBulkIndependentOfVolumeInput : CBulkIndependentOfVolume
    cBulkIndependentOfLatticeSpacingInput : CBulkIndependentOfLatticeSpacing
    cBulkIndependentOfScaleInput : CBulkIndependentOfScale
    cBulkUniformOverAdmissibleBackgroundsInput :
      CBulkUniformOverAdmissibleBackgrounds

    curvaturePerturbation transportPerturbation chartPerturbation
      gaugeFixingPerturbation blockConstraintPerturbation totalPerturbation :
      Index → State → State
    addState : State → State → State

    curvaturePerturbationExactInput : Set
    transportPerturbationExactInput : Set
    chartPerturbationExactInput : Set
    gaugeFixingPerturbationExactInput : Set
    blockConstraintPerturbationExactInput : Set
    fullHessianDifferenceExactInput : ∀ index state →
      fullHessian index state ≡
      addState (bulkHessian index state)
        (addState (curvaturePerturbation index state)
          (addState (transportPerturbation index state)
            (addState (chartPerturbation index state)
              (addState (gaugeFixingPerturbation index state)
                (blockConstraintPerturbation index state)))))

    δCurvature δTransport δChart δGauge δConstraint δTotal : Radius → Bound
    perturbationQuadratic : (Index → State → State) → Index → State → Bound

    curvatureHessianPerturbationBoundInput : ∀ radius index state →
      LessEqual (perturbationQuadratic curvaturePerturbation index state)
        (multiply (δCurvature radius) (normSq state))
    transportHessianPerturbationBoundInput : ∀ radius index state →
      LessEqual (perturbationQuadratic transportPerturbation index state)
        (multiply (δTransport radius) (normSq state))
    chartHessianPerturbationBoundInput : ∀ radius index state →
      LessEqual (perturbationQuadratic chartPerturbation index state)
        (multiply (δChart radius) (normSq state))
    gaugeFixingHessianPerturbationBoundInput : ∀ radius index state →
      LessEqual (perturbationQuadratic gaugeFixingPerturbation index state)
        (multiply (δGauge radius) (normSq state))
    blockConstraintHessianPerturbationBoundInput : ∀ radius index state →
      LessEqual (perturbationQuadratic blockConstraintPerturbation index state)
        (multiply (δConstraint radius) (normSq state))

    totalHessianPerturbationBoundInput : ∀ radius index state →
      LessEqual (perturbationQuadratic totalPerturbation index state)
        (multiply (δTotal radius) (normSq state))
    δTotalMonotoneInput : ∀ {small large} → LessEqual small large →
      LessEqual (δTotal small) (δTotal large)
    δTotalTendsToZeroInput : Set

    selectedRadius : Radius
    cH : Bound
    chooseRadiusWithδTotalBelowBulkGapInput :
      StrictLess (δTotal selectedRadius) cBulk
    uniformConstrainedHessianCoerciveInput : ∀ index state →
      GaugeFixed index state →
      LessEqual (multiply cH (normSq state))
        (inner state (fullHessian index state))
    cHPositiveInput : Positive cH

open BulkHodgeAnalyticInputs public

bulkHessianIsReferenceEnergyOperator = bulkHessianIsReferenceEnergyOperatorInput
bulkHessianPreservesGaugeFixedTangent = bulkHessianPreservesGaugeFixedTangentInput
bulkHessianSelfAdjoint = bulkHessianSelfAdjointInput
bulkHessianPositiveSemidefinite = bulkHessianPositiveSemidefiniteInput
bulkCovariantHodgeIdentity = bulkCovariantHodgeIdentityInput
bulkGaugeFixingTermIdentity = bulkGaugeFixingTermIdentityInput
bulkBlockConstraintTermIdentity = bulkBlockConstraintTermIdentityInput
bulkCurvatureRemainderIdentity = bulkCurvatureRemainderIdentityInput
gaugeExactModesRemoved = gaugeExactModesRemovedInput
blockConstantModesRemoved = blockConstantModesRemovedInput
residualGaugeModesRemoved = residualGaugeModesRemovedInput
constraintKernelTrivial = constraintKernelTrivialInput
referenceEnergyZeroImpliesZero = referenceEnergyZeroImpliesZeroInput
periodicScalarPoincare = periodicScalarPoincareInput
periodicBondPoincare = periodicBondPoincareInput
blockZeroPoincare = blockZeroPoincareInput
covariantPoincareSmallCurvature = covariantPoincareSmallCurvatureInput
bulkGaugeFixedHodgePoincare = bulkGaugeFixedHodgePoincareInput
cBulkPositive = cBulkPositiveInput
cBulkIndependentOfVolume = cBulkIndependentOfVolumeInput
cBulkIndependentOfLatticeSpacing = cBulkIndependentOfLatticeSpacingInput
cBulkIndependentOfScale = cBulkIndependentOfScaleInput
cBulkUniformOverAdmissibleBackgrounds = cBulkUniformOverAdmissibleBackgroundsInput
fullHessianDifferenceExact = fullHessianDifferenceExactInput
curvaturePerturbationExact = curvaturePerturbationExactInput
transportPerturbationExact = transportPerturbationExactInput
chartPerturbationExact = chartPerturbationExactInput
gaugeFixingPerturbationExact = gaugeFixingPerturbationExactInput
blockConstraintPerturbationExact = blockConstraintPerturbationExactInput
curvatureHessianPerturbationBound = curvatureHessianPerturbationBoundInput
transportHessianPerturbationBound = transportHessianPerturbationBoundInput
chartHessianPerturbationBound = chartHessianPerturbationBoundInput
gaugeFixingHessianPerturbationBound = gaugeFixingHessianPerturbationBoundInput
blockConstraintHessianPerturbationBound = blockConstraintHessianPerturbationBoundInput
totalHessianPerturbationBound = totalHessianPerturbationBoundInput
δTotalMonotone = δTotalMonotoneInput
δTotalTendsToZero = δTotalTendsToZeroInput
chooseRadiusWithδTotalBelowBulkGap = chooseRadiusWithδTotalBelowBulkGapInput
uniformConstrainedHessianCoercive = uniformConstrainedHessianCoerciveInput

------------------------------------------------------------------------
-- Bulk Green kernel and weighted Schur estimates.
------------------------------------------------------------------------

record BulkGreenAnalyticInputs
    (Index State Bound Kernel : Set) : Set₁ where
  field
    bulkHessian : Index → State → State
    bulkGreen bulkGradientGreen bulkSecondGradientGreen : Index → State → State
    kernel gradientKernel secondGradientKernel : Index → Kernel
    weightedNorm : State → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    CG CGradG CSecondG : Bound

    bulkGreenKernelExistsInput : ∀ index → Kernel
    bulkGreenKernelRepresentsInverseInput : ∀ index state →
      bulkHessian index (bulkGreen index state) ≡ state
    bulkGreenKernelGaugeCovariantInput : Set
    bulkGreenKernelAdjointSymmetryInput : Set
    bulkGreenLeftInverseInput : ∀ index state →
      bulkGreen index (bulkHessian index state) ≡ state
    bulkGreenRightInverseInput : ∀ index state →
      bulkHessian index (bulkGreen index state) ≡ state

    BulkGreenNearDiagonalBound BulkGreenOffDiagonalDecay
      BulkGreenKernelExponentialDecay : Set
    bulkGreenNearDiagonalBoundInput : BulkGreenNearDiagonalBound
    bulkGreenOffDiagonalDecayInput : BulkGreenOffDiagonalDecay
    bulkGreenKernelExponentialDecayInput : BulkGreenKernelExponentialDecay

    BulkGradientGreenKernelIdentity BulkGradientGreenNearDiagonalBound
      BulkGradientGreenExponentialDecay : Set
    bulkGradientGreenKernelIdentityInput : BulkGradientGreenKernelIdentity
    bulkGradientGreenNearDiagonalBoundInput : BulkGradientGreenNearDiagonalBound
    bulkGradientGreenExponentialDecayInput : BulkGradientGreenExponentialDecay

    BulkSecondGradientGreenKernelIdentity BulkSecondGradientGreenNearDiagonalBound
      BulkSecondGradientGreenExponentialDecay : Set
    bulkSecondGradientGreenKernelIdentityInput :
      BulkSecondGradientGreenKernelIdentity
    bulkSecondGradientGreenNearDiagonalBoundInput :
      BulkSecondGradientGreenNearDiagonalBound
    bulkSecondGradientGreenExponentialDecayInput :
      BulkSecondGradientGreenExponentialDecay

    BulkGreenWeightedRowSum BulkGreenWeightedColumnSum
      BulkGradientGreenWeightedRowSum BulkGradientGreenWeightedColumnSum
      BulkSecondGradientGreenWeightedRowSum
      BulkSecondGradientGreenWeightedColumnSum : Set
    bulkGreenWeightedRowSumInput : BulkGreenWeightedRowSum
    bulkGreenWeightedColumnSumInput : BulkGreenWeightedColumnSum
    bulkGradientGreenWeightedRowSumInput : BulkGradientGreenWeightedRowSum
    bulkGradientGreenWeightedColumnSumInput : BulkGradientGreenWeightedColumnSum
    bulkSecondGradientGreenWeightedRowSumInput :
      BulkSecondGradientGreenWeightedRowSum
    bulkSecondGradientGreenWeightedColumnSumInput :
      BulkSecondGradientGreenWeightedColumnSum

    bulkWeightedGreenBoundInput : ∀ index state →
      LessEqual (weightedNorm (bulkGreen index state))
        (multiply CG (weightedNorm state))
    bulkWeightedGradientGreenBoundInput : ∀ index state →
      LessEqual (weightedNorm (bulkGradientGreen index state))
        (multiply CGradG (weightedNorm state))
    bulkWeightedSecondGradientGreenBoundInput : ∀ index state →
      LessEqual (weightedNorm (bulkSecondGradientGreen index state))
        (multiply CSecondG (weightedNorm state))

    BulkGreenConstantUniformInVolume BulkGreenConstantUniformInSpacing
      BulkGreenConstantUniformInScale BulkGreenConstantUniformInBackground
      BulkGradientConstantUniform BulkSecondGradientConstantUniform : Set
    bulkGreenConstantUniformInVolumeInput : BulkGreenConstantUniformInVolume
    bulkGreenConstantUniformInSpacingInput : BulkGreenConstantUniformInSpacing
    bulkGreenConstantUniformInScaleInput : BulkGreenConstantUniformInScale
    bulkGreenConstantUniformInBackgroundInput : BulkGreenConstantUniformInBackground
    bulkGradientConstantUniformInput : BulkGradientConstantUniform
    bulkSecondGradientConstantUniformInput : BulkSecondGradientConstantUniform

open BulkGreenAnalyticInputs public

bulkGreenKernelExists = bulkGreenKernelExistsInput
bulkGreenKernelRepresentsInverse = bulkGreenKernelRepresentsInverseInput
bulkGreenKernelGaugeCovariant = bulkGreenKernelGaugeCovariantInput
bulkGreenKernelAdjointSymmetry = bulkGreenKernelAdjointSymmetryInput
bulkGreenLeftInverse = bulkGreenLeftInverseInput
bulkGreenRightInverse = bulkGreenRightInverseInput
bulkGreenNearDiagonalBound = bulkGreenNearDiagonalBoundInput
bulkGreenOffDiagonalDecay = bulkGreenOffDiagonalDecayInput
bulkGreenKernelExponentialDecay = bulkGreenKernelExponentialDecayInput
bulkGradientGreenKernelIdentity = bulkGradientGreenKernelIdentityInput
bulkGradientGreenNearDiagonalBound = bulkGradientGreenNearDiagonalBoundInput
bulkGradientGreenExponentialDecay = bulkGradientGreenExponentialDecayInput
bulkSecondGradientGreenKernelIdentity = bulkSecondGradientGreenKernelIdentityInput
bulkSecondGradientGreenNearDiagonalBound = bulkSecondGradientGreenNearDiagonalBoundInput
bulkSecondGradientGreenExponentialDecay = bulkSecondGradientGreenExponentialDecayInput
bulkGreenWeightedRowSum = bulkGreenWeightedRowSumInput
bulkGreenWeightedColumnSum = bulkGreenWeightedColumnSumInput
bulkGradientGreenWeightedRowSum = bulkGradientGreenWeightedRowSumInput
bulkGradientGreenWeightedColumnSum = bulkGradientGreenWeightedColumnSumInput
bulkSecondGradientGreenWeightedRowSum = bulkSecondGradientGreenWeightedRowSumInput
bulkSecondGradientGreenWeightedColumnSum = bulkSecondGradientGreenWeightedColumnSumInput
bulkWeightedGreenBound = bulkWeightedGreenBoundInput
bulkWeightedGradientGreenBound = bulkWeightedGradientGreenBoundInput
bulkWeightedSecondGradientGreenBound = bulkWeightedSecondGradientGreenBoundInput

------------------------------------------------------------------------
-- Four concrete patch geometries and Green intertwining.
------------------------------------------------------------------------

record ConcretePatchGeometry
    (PatchState BulkState Bound : Set) : Set₁ where
  field
    boundaryExtension interfaceExtension cornerExtension nestedExtension :
      PatchState → BulkState
    boundaryRestriction interfaceRestriction cornerRestriction nestedRestriction :
      BulkState → PatchState

    PatchConstraint : PatchState → Set
    BulkConstraint : BulkState → Set
    patchNorm : PatchState → Bound
    bulkNorm : BulkState → Bound
    patchEnergy : PatchState → Bound
    bulkEnergy : BulkState → Bound
    LessEqual : Bound → Bound → Set
    multiply : Bound → Bound → Bound
    CE CR : Bound

    boundaryRestrictionExtensionRetractInput : ∀ h →
      boundaryRestriction (boundaryExtension h) ≡ h
    interfaceRestrictionExtensionRetractInput : ∀ h →
      interfaceRestriction (interfaceExtension h) ≡ h
    cornerRestrictionExtensionRetractInput : ∀ h →
      cornerRestriction (cornerExtension h) ≡ h
    nestedRestrictionExtensionRetractInput : ∀ h →
      nestedRestriction (nestedExtension h) ≡ h

    boundaryExtensionPreservesGaugeConstraintInput : ∀ h →
      PatchConstraint h → BulkConstraint (boundaryExtension h)
    boundaryExtensionPreservesBlockConstraintInput : ∀ h →
      PatchConstraint h → BulkConstraint (boundaryExtension h)
    interfaceExtensionPreservesConstraintsInput : ∀ h →
      PatchConstraint h → BulkConstraint (interfaceExtension h)
    cornerExtensionPreservesConstraintsInput : ∀ h →
      PatchConstraint h → BulkConstraint (cornerExtension h)
    nestedExtensionPreservesConstraintsInput : ∀ h →
      PatchConstraint h → BulkConstraint (nestedExtension h)

    boundaryExtensionWeightedNormBoundInput : ∀ h →
      LessEqual (bulkNorm (boundaryExtension h)) (multiply CE (patchNorm h))
    interfaceExtensionWeightedNormBoundInput : ∀ h →
      LessEqual (bulkNorm (interfaceExtension h)) (multiply CE (patchNorm h))
    cornerExtensionWeightedNormBoundInput : ∀ h →
      LessEqual (bulkNorm (cornerExtension h)) (multiply CE (patchNorm h))
    nestedExtensionWeightedNormBoundInput : ∀ h →
      LessEqual (bulkNorm (nestedExtension h)) (multiply CE (patchNorm h))

    boundaryRestrictionWeightedNormBoundInput : ∀ h →
      LessEqual (patchNorm (boundaryRestriction h)) (multiply CR (bulkNorm h))
    interfaceRestrictionWeightedNormBoundInput : ∀ h →
      LessEqual (patchNorm (interfaceRestriction h)) (multiply CR (bulkNorm h))
    cornerRestrictionWeightedNormBoundInput : ∀ h →
      LessEqual (patchNorm (cornerRestriction h)) (multiply CR (bulkNorm h))
    nestedRestrictionWeightedNormBoundInput : ∀ h →
      LessEqual (patchNorm (nestedRestriction h)) (multiply CR (bulkNorm h))

    boundaryEnergyComparedToBulkInput : ∀ h →
      LessEqual (bulkEnergy (boundaryExtension h)) (patchEnergy h)
    interfaceEnergyComparedToBulkInput : ∀ h →
      LessEqual (bulkEnergy (interfaceExtension h)) (patchEnergy h)
    cornerEnergyComparedToBulkInput : ∀ h →
      LessEqual (bulkEnergy (cornerExtension h)) (patchEnergy h)
    nestedEnergyComparedToBulkInput : ∀ h →
      LessEqual (bulkEnergy (nestedExtension h)) (patchEnergy h)

    bulkGreen bulkGradientGreen bulkSecondGradientGreen : BulkState → BulkState
    boundaryGreen interfaceGreen cornerGreen nestedGreen : PatchState → PatchState
    boundaryGradientGreen interfaceGradientGreen cornerGradientGreen
      nestedGradientGreen : PatchState → PatchState
    boundarySecondGradientGreen interfaceSecondGradientGreen cornerSecondGradientGreen
      nestedSecondGradientGreen : PatchState → PatchState

    boundaryGreenIntertwiningInput : ∀ f →
      boundaryGreen f ≡ boundaryRestriction (bulkGreen (boundaryExtension f))
    interfaceGreenIntertwiningInput : ∀ f →
      interfaceGreen f ≡ interfaceRestriction (bulkGreen (interfaceExtension f))
    cornerGreenIntertwiningInput : ∀ f →
      cornerGreen f ≡ cornerRestriction (bulkGreen (cornerExtension f))
    nestedGreenIntertwiningInput : ∀ f →
      nestedGreen f ≡ nestedRestriction (bulkGreen (nestedExtension f))

    boundaryGradientGreenIntertwiningInput : ∀ f →
      boundaryGradientGreen f ≡
      boundaryRestriction (bulkGradientGreen (boundaryExtension f))
    interfaceGradientGreenIntertwiningInput : ∀ f →
      interfaceGradientGreen f ≡
      interfaceRestriction (bulkGradientGreen (interfaceExtension f))
    cornerGradientGreenIntertwiningInput : ∀ f →
      cornerGradientGreen f ≡
      cornerRestriction (bulkGradientGreen (cornerExtension f))
    nestedGradientGreenIntertwiningInput : ∀ f →
      nestedGradientGreen f ≡
      nestedRestriction (bulkGradientGreen (nestedExtension f))

    boundarySecondGradientGreenIntertwiningInput : ∀ f →
      boundarySecondGradientGreen f ≡
      boundaryRestriction (bulkSecondGradientGreen (boundaryExtension f))
    interfaceSecondGradientGreenIntertwiningInput : ∀ f →
      interfaceSecondGradientGreen f ≡
      interfaceRestriction (bulkSecondGradientGreen (interfaceExtension f))
    cornerSecondGradientGreenIntertwiningInput : ∀ f →
      cornerSecondGradientGreen f ≡
      cornerRestriction (bulkSecondGradientGreen (cornerExtension f))
    nestedSecondGradientGreenIntertwiningInput : ∀ f →
      nestedSecondGradientGreen f ≡
      nestedRestriction (bulkSecondGradientGreen (nestedExtension f))

    BoundaryGreenCorrectionBound InterfaceGreenCorrectionBound
      CornerGreenCorrectionBound NestedGreenCorrectionBound : Set
    boundaryGreenCorrectionBoundInput : BoundaryGreenCorrectionBound
    interfaceGreenCorrectionBoundInput : InterfaceGreenCorrectionBound
    cornerGreenCorrectionBoundInput : CornerGreenCorrectionBound
    nestedGreenCorrectionBoundInput : NestedGreenCorrectionBound

open ConcretePatchGeometry public

concreteBoundaryExtension = boundaryExtension
concreteBoundaryRestriction = boundaryRestriction
concreteInterfaceExtension = interfaceExtension
concreteInterfaceRestriction = interfaceRestriction
concreteCornerExtension = cornerExtension
concreteCornerRestriction = cornerRestriction
concreteNestedExtension = nestedExtension
concreteNestedRestriction = nestedRestriction
boundaryRestrictionExtensionRetract = boundaryRestrictionExtensionRetractInput
interfaceRestrictionExtensionRetract = interfaceRestrictionExtensionRetractInput
cornerRestrictionExtensionRetract = cornerRestrictionExtensionRetractInput
nestedRestrictionExtensionRetract = nestedRestrictionExtensionRetractInput
boundaryExtensionPreservesGaugeConstraint = boundaryExtensionPreservesGaugeConstraintInput
boundaryExtensionPreservesBlockConstraint = boundaryExtensionPreservesBlockConstraintInput
interfaceExtensionPreservesConstraints = interfaceExtensionPreservesConstraintsInput
cornerExtensionPreservesConstraints = cornerExtensionPreservesConstraintsInput
nestedExtensionPreservesConstraints = nestedExtensionPreservesConstraintsInput
boundaryExtensionWeightedNormBound = boundaryExtensionWeightedNormBoundInput
interfaceExtensionWeightedNormBound = interfaceExtensionWeightedNormBoundInput
cornerExtensionWeightedNormBound = cornerExtensionWeightedNormBoundInput
nestedExtensionWeightedNormBound = nestedExtensionWeightedNormBoundInput
boundaryRestrictionWeightedNormBound = boundaryRestrictionWeightedNormBoundInput
interfaceRestrictionWeightedNormBound = interfaceRestrictionWeightedNormBoundInput
cornerRestrictionWeightedNormBound = cornerRestrictionWeightedNormBoundInput
nestedRestrictionWeightedNormBound = nestedRestrictionWeightedNormBoundInput
boundaryEnergyComparedToBulk = boundaryEnergyComparedToBulkInput
interfaceEnergyComparedToBulk = interfaceEnergyComparedToBulkInput
cornerEnergyComparedToBulk = cornerEnergyComparedToBulkInput
nestedEnergyComparedToBulk = nestedEnergyComparedToBulkInput
boundaryGreenIntertwining = boundaryGreenIntertwiningInput
interfaceGreenIntertwining = interfaceGreenIntertwiningInput
cornerGreenIntertwining = cornerGreenIntertwiningInput
nestedGreenIntertwining = nestedGreenIntertwiningInput
boundaryGradientGreenIntertwining = boundaryGradientGreenIntertwiningInput
interfaceGradientGreenIntertwining = interfaceGradientGreenIntertwiningInput
cornerGradientGreenIntertwining = cornerGradientGreenIntertwiningInput
nestedGradientGreenIntertwining = nestedGradientGreenIntertwiningInput
boundarySecondGradientGreenIntertwining = boundarySecondGradientGreenIntertwiningInput
interfaceSecondGradientGreenIntertwining = interfaceSecondGradientGreenIntertwiningInput
cornerSecondGradientGreenIntertwining = cornerSecondGradientGreenIntertwiningInput
nestedSecondGradientGreenIntertwining = nestedSecondGradientGreenIntertwiningInput
boundaryGreenCorrectionBound = boundaryGreenCorrectionBoundInput
interfaceGreenCorrectionBound = interfaceGreenCorrectionBoundInput
cornerGreenCorrectionBound = cornerGreenCorrectionBoundInput
nestedGreenCorrectionBound = nestedGreenCorrectionBoundInput

------------------------------------------------------------------------
-- Local parametrix, strict residual and Neumann closure.
------------------------------------------------------------------------

record ParametrixResidualAnalyticInputs
    (Index State Bound : Set) : Set₁ where
  field
    localGreen residual correctionInverse fullGreen gradientFullGreen
      secondGradientFullGreen : Index → State → State
    residualPower partialSum tail : Index → Nat → State → State
    H : Index → State → State
    subtract : State → State → State
    weightedNorm : State → Bound
    multiply pow : Bound → Bound → Bound
    LessEqual StrictLess : Bound → Bound → Set
    one qCommon Ccorr CG CGradG CSecondG : Bound

    LocalPartitionOfUnity LocalPartitionFiniteOverlap
      LocalPartitionGradientBound LocalPartitionSecondGradientBound
      SupportContainedInEnlargedPatch : Set
    localPartitionOfUnityInput : LocalPartitionOfUnity
    localPartitionFiniteOverlapInput : LocalPartitionFiniteOverlap
    localPartitionGradientBoundInput : LocalPartitionGradientBound
    localPartitionSecondGradientBoundInput : LocalPartitionSecondGradientBound
    supportContainedInEnlargedPatchInput : SupportContainedInEnlargedPatch

    LocalHessianInverseExists LocalGreenWeightedBound
      LocalGradientGreenWeightedBound LocalSecondGradientGreenWeightedBound : Set
    localHessianInverseExistsInput : LocalHessianInverseExists
    localGreenWeightedBoundInput : LocalGreenWeightedBound
    localGradientGreenWeightedBoundInput : LocalGradientGreenWeightedBound
    localSecondGradientGreenWeightedBoundInput : LocalSecondGradientGreenWeightedBound

    LocalParametrixDefinition : Set
    localParametrixDefinitionInput : LocalParametrixDefinition
    localParametrixResidualEquationInput : ∀ index f →
      H index (localGreen index f) ≡ subtract f (residual index f)

    ResidualDecomposes ResidualLocalizationCommutatorPart ResidualOverlapPart
      ResidualBoundaryPart ResidualInterfacePart ResidualCornerPart
      ResidualNestedPart ResidualBackgroundPart : Set
    residualDecomposesInput : ResidualDecomposes
    residualLocalizationCommutatorPartInput : ResidualLocalizationCommutatorPart
    residualOverlapPartInput : ResidualOverlapPart
    residualBoundaryPartInput : ResidualBoundaryPart
    residualInterfacePartInput : ResidualInterfacePart
    residualCornerPartInput : ResidualCornerPart
    residualNestedPartInput : ResidualNestedPart
    residualBackgroundPartInput : ResidualBackgroundPart

    LocalizationCommutatorResidualBound OverlapResidualBound
      BoundaryResidualBound InterfaceResidualBound CornerResidualBound
      NestedResidualBound BackgroundResidualBound : Set
    localizationCommutatorResidualBoundInput : LocalizationCommutatorResidualBound
    overlapResidualBoundInput : OverlapResidualBound
    boundaryResidualBoundInput : BoundaryResidualBound
    interfaceResidualBoundInput : InterfaceResidualBound
    cornerResidualBoundInput : CornerResidualBound
    nestedResidualBoundInput : NestedResidualBound
    backgroundResidualBoundInput : BackgroundResidualBound

    bulkWeightedResidualBoundInput : ∀ index f →
      LessEqual (weightedNorm (residual index f))
        (multiply qCommon (weightedNorm f))
    PatchResidualControlledByBulk EachResidualBelowCommon QCommonPositive : Set
    patchResidualControlledByBulkInput : PatchResidualControlledByBulk
    eachResidualBelowCommonInput : EachResidualBelowCommon
    qCommonPositiveInput : QCommonPositive
    qCommonStrictInput : StrictLess qCommon one

    residualPowerBoundInput : ∀ index n f →
      LessEqual (weightedNorm (residualPower index n f))
        (multiply qCommon (weightedNorm f))
    GeometricResidualTailBound NeumannSeriesConverges CorrectionInverseExists : Set
    geometricResidualTailBoundInput : GeometricResidualTailBound
    neumannSeriesConvergesInput : NeumannSeriesConverges
    correctionInverseExistsInput : CorrectionInverseExists
    uniformCorrectionInverseBoundInput : ∀ index f →
      LessEqual (weightedNorm (correctionInverse index f))
        (multiply Ccorr (weightedNorm f))

    FullGreenFactorization : Set
    fullGreenFactorizationInput : FullGreenFactorization
    uniformWeightedGreenBoundInput : ∀ index f →
      LessEqual (weightedNorm (fullGreen index f))
        (multiply CG (weightedNorm f))
    uniformWeightedGradientGreenBoundInput : ∀ index f →
      LessEqual (weightedNorm (gradientFullGreen index f))
        (multiply CGradG (weightedNorm f))
    uniformWeightedSecondGradientGreenBoundInput : ∀ index f →
      LessEqual (weightedNorm (secondGradientFullGreen index f))
        (multiply CSecondG (weightedNorm f))

open ParametrixResidualAnalyticInputs public

localPartitionOfUnity = localPartitionOfUnityInput
localPartitionFiniteOverlap = localPartitionFiniteOverlapInput
localPartitionGradientBound = localPartitionGradientBoundInput
localPartitionSecondGradientBound = localPartitionSecondGradientBoundInput
supportContainedInEnlargedPatch = supportContainedInEnlargedPatchInput
localHessianInverseExists = localHessianInverseExistsInput
localGreenWeightedBound = localGreenWeightedBoundInput
localGradientGreenWeightedBound = localGradientGreenWeightedBoundInput
localSecondGradientGreenWeightedBound = localSecondGradientGreenWeightedBoundInput
localParametrixDefinition = localParametrixDefinitionInput
localParametrixResidualEquation = localParametrixResidualEquationInput
residualDecomposes = residualDecomposesInput
residualLocalizationCommutatorPart = residualLocalizationCommutatorPartInput
residualOverlapPart = residualOverlapPartInput
residualBoundaryPart = residualBoundaryPartInput
residualInterfacePart = residualInterfacePartInput
residualCornerPart = residualCornerPartInput
residualNestedPart = residualNestedPartInput
residualBackgroundPart = residualBackgroundPartInput
localizationCommutatorResidualBound = localizationCommutatorResidualBoundInput
overlapResidualBound = overlapResidualBoundInput
boundaryResidualBound = boundaryResidualBoundInput
interfaceResidualBound = interfaceResidualBoundInput
cornerResidualBound = cornerResidualBoundInput
nestedResidualBound = nestedResidualBoundInput
backgroundResidualBound = backgroundResidualBoundInput
bulkWeightedResidualBound = bulkWeightedResidualBoundInput
patchResidualControlledByBulk = patchResidualControlledByBulkInput
eachResidualBelowCommon = eachResidualBelowCommonInput
qCommonPositive = qCommonPositiveInput
qCommonStrict = qCommonStrictInput
residualPowerBound = residualPowerBoundInput
geometricResidualTailBound = geometricResidualTailBoundInput
neumannSeriesConverges = neumannSeriesConvergesInput
correctionInverseExists = correctionInverseExistsInput
uniformCorrectionInverseBound = uniformCorrectionInverseBoundInput
fullGreenFactorization = fullGreenFactorizationInput
uniformWeightedGreenBound = uniformWeightedGreenBoundInput
uniformWeightedGradientGreenBound = uniformWeightedGradientGreenBoundInput
uniformWeightedSecondGradientGreenBound = uniformWeightedSecondGradientGreenBoundInput

------------------------------------------------------------------------
-- Seven nonlinear mechanisms and the common contraction constant.
------------------------------------------------------------------------

record SevenNonlinearAnalyticInputs
    (Index State Bound Radius : Set) : Set₁ where
  field
    nonlinear NBCH Ncomm Ntransport NbackgroundDerivative Ngauge
      Nconstraint Nchart : Index → State → State
    subtract : State → State → State
    norm : State → Bound
    multiply : Bound → Bound → Bound
    LessEqual StrictLess : Bound → Bound → Set
    InCriticalBall : Index → State → Set
    radius : Radius
    LBCH Lcomm Ltransport LbackgroundDerivative Lgauge Lconstraint Lchart LN :
      Radius → Bound

    CompactLieBracketInequality BCHThirdOrderRemainderBound
      BCHDerivativeDifferenceBound : Set
    compactLieBracketInequalityInput : CompactLieBracketInequality
    bchThirdOrderRemainderBoundInput : BCHThirdOrderRemainderBound
    bchDerivativeDifferenceBoundInput : BCHDerivativeDifferenceBound

    bchHigherLipschitzInput : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (NBCH index h) (NBCH index h′)))
        (multiply (LBCH radius) (norm (subtract h h′)))
    commutatorRemainderLipschitzInput : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Ncomm index h) (Ncomm index h′)))
        (multiply (Lcomm radius) (norm (subtract h h′)))
    parallelTransportRemainderLipschitzInput : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Ntransport index h) (Ntransport index h′)))
        (multiply (Ltransport radius) (norm (subtract h h′)))
    backgroundDerivativeRemainderLipschitzInput : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual
        (norm (subtract (NbackgroundDerivative index h)
          (NbackgroundDerivative index h′)))
        (multiply (LbackgroundDerivative radius) (norm (subtract h h′)))
    gaugeFixingRemainderLipschitzInput : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Ngauge index h) (Ngauge index h′)))
        (multiply (Lgauge radius) (norm (subtract h h′)))
    blockConstraintRemainderLipschitzInput : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Nconstraint index h) (Nconstraint index h′)))
        (multiply (Lconstraint radius) (norm (subtract h h′)))
    chartChangeRemainderLipschitzInput : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (Nchart index h) (Nchart index h′)))
        (multiply (Lchart radius) (norm (subtract h h′)))

    CommutatorRemainderExact ParallelTransportDifferenceExact
      BackgroundDerivativeDifferenceExact GaugeFixingNonlinearDifferenceExact
      BlockConstraintNonlinearDifferenceExact ChartChangeDifferenceExact
      NonlinearDifferenceExactSevenPartDecomposition : Set
    commutatorRemainderExactInput : CommutatorRemainderExact
    parallelTransportDifferenceExactInput : ParallelTransportDifferenceExact
    backgroundDerivativeDifferenceExactInput : BackgroundDerivativeDifferenceExact
    gaugeFixingNonlinearDifferenceExactInput : GaugeFixingNonlinearDifferenceExact
    blockConstraintNonlinearDifferenceExactInput :
      BlockConstraintNonlinearDifferenceExact
    chartChangeDifferenceExactInput : ChartChangeDifferenceExact
    nonlinearDifferenceExactSevenPartDecompositionInput :
      NonlinearDifferenceExactSevenPartDecomposition

    SevenComponentConstantBound LNMonotone LNTendsToZero : Set
    sevenComponentConstantBoundInput : SevenComponentConstantBound
    LNMonotoneInput : LNMonotone
    LNTendsToZeroInput : LNTendsToZero
    uniformNonlinearRemainderLipschitzInput : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtract (nonlinear index h) (nonlinear index h′)))
        (multiply (LN radius) (norm (subtract h h′)))

open SevenNonlinearAnalyticInputs public

compactLieBracketInequality = compactLieBracketInequalityInput
bchThirdOrderRemainderBound = bchThirdOrderRemainderBoundInput
bchDerivativeDifferenceBound = bchDerivativeDifferenceBoundInput
bchHigherLipschitz = bchHigherLipschitzInput
commutatorRemainderExact = commutatorRemainderExactInput
commutatorRemainderLipschitz = commutatorRemainderLipschitzInput
parallelTransportDifferenceExact = parallelTransportDifferenceExactInput
parallelTransportRemainderLipschitz = parallelTransportRemainderLipschitzInput
backgroundDerivativeDifferenceExact = backgroundDerivativeDifferenceExactInput
backgroundDerivativeRemainderLipschitz = backgroundDerivativeRemainderLipschitzInput
gaugeFixingNonlinearDifferenceExact = gaugeFixingNonlinearDifferenceExactInput
gaugeFixingRemainderLipschitz = gaugeFixingRemainderLipschitzInput
blockConstraintNonlinearDifferenceExact = blockConstraintNonlinearDifferenceExactInput
blockConstraintRemainderLipschitz = blockConstraintRemainderLipschitzInput
chartChangeDifferenceExact = chartChangeDifferenceExactInput
chartChangeRemainderLipschitz = chartChangeRemainderLipschitzInput
nonlinearDifferenceExactSevenPartDecomposition =
  nonlinearDifferenceExactSevenPartDecompositionInput
sevenComponentConstantBound = sevenComponentConstantBoundInput
LNMonotone = LNMonotoneInput
LNTendsToZero = LNTendsToZeroInput
uniformNonlinearRemainderLipschitz = uniformNonlinearRemainderLipschitzInput

record BulkPropagatorAnalyticCertificate
    (Index State ScalarState Force Bound Kernel Radius PatchState BulkState : Set)
    : Set₁ where
  field
    hodge : BulkHodgeAnalyticInputs Index State ScalarState Bound Radius
    green : BulkGreenAnalyticInputs Index Force Bound Kernel
    patches : ConcretePatchGeometry PatchState BulkState Bound
    residual : ParametrixResidualAnalyticInputs Index Force Bound
    nonlinear : SevenNonlinearAnalyticInputs Index State Bound Radius

open BulkPropagatorAnalyticCertificate public

bulkPropagatorAssemblyLevel : ProofLevel
bulkPropagatorAssemblyLevel = machineChecked

bulkHodgeAnalyticInputLevel : ProofLevel
bulkHodgeAnalyticInputLevel = conditional

bulkGreenAnalyticInputLevel : ProofLevel
bulkGreenAnalyticInputLevel = conditional

concretePatchGeometryAnalyticInputLevel : ProofLevel
concretePatchGeometryAnalyticInputLevel = conditional

strictResidualAnalyticInputLevel : ProofLevel
strictResidualAnalyticInputLevel = conditional

sevenNonlinearAnalyticInputLevel : ProofLevel
sevenNonlinearAnalyticInputLevel = conditional
