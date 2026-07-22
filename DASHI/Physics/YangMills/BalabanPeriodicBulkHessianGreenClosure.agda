module DASHI.Physics.YangMills.BalabanPeriodicBulkHessianGreenClosure where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicBlockSymbolGap
open import DASHI.Physics.YangMills.BalabanPeriodicLocalBlockGapInhabitation
open import DASHI.Physics.YangMills.BalabanPeriodicFiniteFourierHodgeCertificate

------------------------------------------------------------------------
-- Coherent periodic bulk Hessian and Green closure.
--
-- This module consumes the literal periodic Hodge certificate and the five
-- concrete background-Hessian perturbation bounds in one owner.  It proves the
-- relative-form coercivity theorem and then records the exact finite inverse,
-- weighted Green and kernel-decay conclusions that must be supplied either by
-- finite-dimensional coercive inversion or by the source-faithful Balaban
-- propagator theorem after exact carrier matching.
------------------------------------------------------------------------

record PeriodicBulkHessianGreenInputs
    {Index State Frequency Bound Kernel : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData}
    (gapInputs : PhysicalLocalBlockGapInputs constraints) : Set₁ where
  field
    referenceHessian fullHessian : Index → State → State
    inner : State → State → Bound

    referenceEnergyIsInner : ∀ index state →
      referenceEnergy symbolData index state ≡
      inner state (referenceHessian index state)

    perturbationEnergy : Index → State → Bound
    curvaturePart transportPart chartPart gaugeFixingPart
      blockConstraintPart : Index → State → Bound

    curvatureUpper transportUpper chartUpper gaugeFixingUpper
      blockConstraintUpper perturbationUpper : Bound

    perturbationBelowFiveParts : ∀ index state →
      LessEqual (ordered symbolData)
        (perturbationEnergy index state)
        (add (ordered symbolData) (curvaturePart index state)
          (add (ordered symbolData) (transportPart index state)
            (add (ordered symbolData) (chartPart index state)
              (add (ordered symbolData) (gaugeFixingPart index state)
                (blockConstraintPart index state)))))

    curvaturePerturbationBound : ∀ index state →
      LessEqual (ordered symbolData)
        (curvaturePart index state)
        (scale (ordered symbolData) curvatureUpper
          (normSq symbolData state))

    transportPerturbationBound : ∀ index state →
      LessEqual (ordered symbolData)
        (transportPart index state)
        (scale (ordered symbolData) transportUpper
          (normSq symbolData state))

    chartPerturbationBound : ∀ index state →
      LessEqual (ordered symbolData)
        (chartPart index state)
        (scale (ordered symbolData) chartUpper
          (normSq symbolData state))

    gaugeFixingPerturbationBound : ∀ index state →
      LessEqual (ordered symbolData)
        (gaugeFixingPart index state)
        (scale (ordered symbolData) gaugeFixingUpper
          (normSq symbolData state))

    blockConstraintPerturbationBound : ∀ index state →
      LessEqual (ordered symbolData)
        (blockConstraintPart index state)
        (scale (ordered symbolData) blockConstraintUpper
          (normSq symbolData state))

    combineFiveScaledBounds : ∀ state →
      add (ordered symbolData)
        (scale (ordered symbolData) curvatureUpper (normSq symbolData state))
        (add (ordered symbolData)
          (scale (ordered symbolData) transportUpper (normSq symbolData state))
          (add (ordered symbolData)
            (scale (ordered symbolData) chartUpper (normSq symbolData state))
            (add (ordered symbolData)
              (scale (ordered symbolData) gaugeFixingUpper
                (normSq symbolData state))
              (scale (ordered symbolData) blockConstraintUpper
                (normSq symbolData state)))))
      ≡ scale (ordered symbolData) perturbationUpper
          (normSq symbolData state)

    referenceBelowFullPlusPerturbation : ∀ index state →
      GaugeFixedTangent constraints index state →
      LessEqual (ordered symbolData)
        (inner state (referenceHessian index state))
        (add (ordered symbolData)
          (inner state (fullHessian index state))
          (perturbationEnergy index state))

    cH : Bound
    cHPositive : Positive (ordered symbolData) cH

    coercivityBudget : ∀ state →
      LessEqual (ordered symbolData)
        (add (ordered symbolData)
          (scale (ordered symbolData) cH (normSq symbolData state))
          (scale (ordered symbolData) perturbationUpper
            (normSq symbolData state)))
        (scale (ordered symbolData) (cBulk gapInputs)
          (normSq symbolData state))

    reflexive : ∀ value → LessEqual (ordered symbolData) value value
    addMonotone : ∀ {left left′ right right′} →
      LessEqual (ordered symbolData) left left′ →
      LessEqual (ordered symbolData) right right′ →
      LessEqual (ordered symbolData)
        (add (ordered symbolData) left right)
        (add (ordered symbolData) left′ right′)

    addRightCancel : ∀ {left right common} →
      LessEqual (ordered symbolData)
        (add (ordered symbolData) left common)
        (add (ordered symbolData) right common) →
      LessEqual (ordered symbolData) left right

    -- Selected constrained inverse and operator-norm estimate.
    green gradientGreen secondGradientGreen : Index → State → State
    greenLeftInverse : ∀ index state →
      green index (fullHessian index state) ≡ state
    greenRightInverse : ∀ index state →
      fullHessian index (green index state) ≡ state

    weightedNorm : State → Bound
    multiplyBound : Bound → Bound → Bound
    reciprocalCH CG CGradG CSecondGradG : Bound

    reciprocalCHMatchesGreenConstant : reciprocalCH ≡ CG

    bulkWeightedGreenBound : ∀ index source →
      LessEqual (ordered symbolData)
        (weightedNorm (green index source))
        (multiplyBound CG (weightedNorm source))

    bulkWeightedGradientGreenBound : ∀ index source →
      LessEqual (ordered symbolData)
        (weightedNorm (gradientGreen index source))
        (multiplyBound CGradG (weightedNorm source))

    bulkWeightedSecondGradientGreenBound : ∀ index source →
      LessEqual (ordered symbolData)
        (weightedNorm (secondGradientGreen index source))
        (multiplyBound CSecondGradG (weightedNorm source))

    greenKernel gradientGreenKernel secondGradientGreenKernel : Index → Kernel
    KernelExponentialDecay : Kernel → Set

    bulkGreenKernelExponentialDecay : ∀ index →
      KernelExponentialDecay (greenKernel index)
    bulkGradientGreenKernelExponentialDecay : ∀ index →
      KernelExponentialDecay (gradientGreenKernel index)
    bulkSecondGradientGreenKernelExponentialDecay : ∀ index →
      KernelExponentialDecay (secondGradientGreenKernel index)

    BulkGreenConstantUniformInVolume BulkGreenConstantUniformInSpacing
      BulkGreenConstantUniformInScale BulkGreenConstantUniformInBackground : Set

    bulkGreenConstantUniformInVolume : BulkGreenConstantUniformInVolume
    bulkGreenConstantUniformInSpacing : BulkGreenConstantUniformInSpacing
    bulkGreenConstantUniformInScale : BulkGreenConstantUniformInScale
    bulkGreenConstantUniformInBackground : BulkGreenConstantUniformInBackground

open PeriodicBulkHessianGreenInputs public

fiveComponentHessianPerturbationBound :
  ∀ {Index State Frequency Bound Kernel : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData}
    {gapInputs : PhysicalLocalBlockGapInputs constraints} →
    (inputs : PeriodicBulkHessianGreenInputs {Kernel = Kernel} gapInputs) →
    ∀ index state →
    LessEqual (ordered symbolData)
      (perturbationEnergy inputs index state)
      (scale (ordered symbolData) (perturbationUpper inputs)
        (normSq symbolData state))
fiveComponentHessianPerturbationBound {symbolData = symbolData}
  inputs index state
  rewrite combineFiveScaledBounds inputs state =
  lessEqualTransitive (ordered symbolData)
    (perturbationBelowFiveParts inputs index state)
    (addMonotone inputs
      (curvaturePerturbationBound inputs index state)
      (addMonotone inputs
        (transportPerturbationBound inputs index state)
        (addMonotone inputs
          (chartPerturbationBound inputs index state)
          (addMonotone inputs
            (gaugeFixingPerturbationBound inputs index state)
            (blockConstraintPerturbationBound inputs index state)))))

periodicReferenceHessianCoercive :
  ∀ {Index State Frequency Bound Kernel : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData}
    {gapInputs : PhysicalLocalBlockGapInputs constraints} →
    (inputs : PeriodicBulkHessianGreenInputs {Kernel = Kernel} gapInputs) →
    ∀ index state →
    GaugeFixedTangent constraints index state →
    LessEqual (ordered symbolData)
      (scale (ordered symbolData) (cBulk gapInputs)
        (normSq symbolData state))
      (inner inputs state (referenceHessian inputs index state))
periodicReferenceHessianCoercive {symbolData = symbolData}
  {kernelData = kernelData} {constraints = constraints}
  {gapInputs = gapInputs} inputs index state tangent
  rewrite referenceEnergyIsInner inputs index state =
  periodicBulkGaugeFixedHodgePoincare
    symbolData kernelData constraints
    (physicalPeriodicBlockGapData gapInputs)
    index state tangent

uniformConstrainedHessianCoercive :
  ∀ {Index State Frequency Bound Kernel : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData}
    {gapInputs : PhysicalLocalBlockGapInputs constraints} →
    (inputs : PeriodicBulkHessianGreenInputs {Kernel = Kernel} gapInputs) →
    ∀ index state →
    GaugeFixedTangent constraints index state →
    LessEqual (ordered symbolData)
      (scale (ordered symbolData) (cH inputs) (normSq symbolData state))
      (inner inputs state (fullHessian inputs index state))
uniformConstrainedHessianCoercive {symbolData = symbolData}
  inputs index state tangent =
  addRightCancel inputs
    (lessEqualTransitive (ordered symbolData)
      (coercivityBudget inputs state)
      (lessEqualTransitive (ordered symbolData)
        (periodicReferenceHessianCoercive inputs index state tangent)
        (lessEqualTransitive (ordered symbolData)
          (referenceBelowFullPlusPerturbation inputs index state tangent)
          (addMonotone inputs
            (reflexive inputs (inner inputs state
              (fullHessian inputs index state)))
            (fiveComponentHessianPerturbationBound inputs index state)))))

record PeriodicBulkHessianGreenCertificate
    (Index State Bound Kernel : Set) : Set₁ where
  field
    fullHessian green gradientGreen secondGradientGreen : Index → State → State
    inner : State → State → Bound
    normSq weightedNorm : State → Bound
    scale multiplyBound : Bound → Bound → Bound
    LessEqual Positive : Bound → Bound → Set
    cH CG CGradG CSecondGradG : Bound

    cHPositive : Positive cH cH
    GaugeFixedTangent : Index → State → Set

    uniformConstrainedHessianCoercive : ∀ index state →
      GaugeFixedTangent index state →
      LessEqual (scale cH (normSq state))
        (inner state (fullHessian index state))

    greenLeftInverse : ∀ index state →
      green index (fullHessian index state) ≡ state
    greenRightInverse : ∀ index state →
      fullHessian index (green index state) ≡ state

    weightedGreenBound : ∀ index source →
      LessEqual (weightedNorm (green index source))
        (multiplyBound CG (weightedNorm source))
    weightedGradientGreenBound : ∀ index source →
      LessEqual (weightedNorm (gradientGreen index source))
        (multiplyBound CGradG (weightedNorm source))
    weightedSecondGradientGreenBound : ∀ index source →
      LessEqual (weightedNorm (secondGradientGreen index source))
        (multiplyBound CSecondGradG (weightedNorm source))

    greenKernel gradientGreenKernel secondGradientGreenKernel : Index → Kernel
    KernelExponentialDecay : Kernel → Set
    greenKernelDecay : ∀ index → KernelExponentialDecay (greenKernel index)
    gradientGreenKernelDecay : ∀ index →
      KernelExponentialDecay (gradientGreenKernel index)
    secondGradientGreenKernelDecay : ∀ index →
      KernelExponentialDecay (secondGradientGreenKernel index)

open PeriodicBulkHessianGreenCertificate public

periodicBulkHessianGreenCertificate :
  ∀ {Index State Frequency Bound Kernel : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData}
    {gapInputs : PhysicalLocalBlockGapInputs constraints} →
    (inputs : PeriodicBulkHessianGreenInputs {Kernel = Kernel} gapInputs) →
    PeriodicBulkHessianGreenCertificate Index State Bound Kernel
periodicBulkHessianGreenCertificate {symbolData = symbolData}
  {constraints = constraints} inputs = record
  { fullHessian = fullHessian inputs
  ; green = green inputs
  ; gradientGreen = gradientGreen inputs
  ; secondGradientGreen = secondGradientGreen inputs
  ; inner = inner inputs
  ; normSq = normSq symbolData
  ; weightedNorm = weightedNorm inputs
  ; scale = scale (ordered symbolData)
  ; multiplyBound = multiplyBound inputs
  ; LessEqual = LessEqual (ordered symbolData)
  ; Positive = λ left right → Positive (ordered symbolData) left
  ; cH = cH inputs
  ; CG = CG inputs
  ; CGradG = CGradG inputs
  ; CSecondGradG = CSecondGradG inputs
  ; cHPositive = cHPositive inputs
  ; GaugeFixedTangent = GaugeFixedTangent constraints
  ; uniformConstrainedHessianCoercive =
      uniformConstrainedHessianCoercive inputs
  ; greenLeftInverse = greenLeftInverse inputs
  ; greenRightInverse = greenRightInverse inputs
  ; weightedGreenBound = bulkWeightedGreenBound inputs
  ; weightedGradientGreenBound = bulkWeightedGradientGreenBound inputs
  ; weightedSecondGradientGreenBound =
      bulkWeightedSecondGradientGreenBound inputs
  ; greenKernel = greenKernel inputs
  ; gradientGreenKernel = gradientGreenKernel inputs
  ; secondGradientGreenKernel = secondGradientGreenKernel inputs
  ; KernelExponentialDecay = KernelExponentialDecay inputs
  ; greenKernelDecay = bulkGreenKernelExponentialDecay inputs
  ; gradientGreenKernelDecay = bulkGradientGreenKernelExponentialDecay inputs
  ; secondGradientGreenKernelDecay =
      bulkSecondGradientGreenKernelExponentialDecay inputs
  }

periodicFivePerturbationAssemblyLevel : ProofLevel
periodicFivePerturbationAssemblyLevel = machineChecked

periodicFullHessianCoercivityAssemblyLevel : ProofLevel
periodicFullHessianCoercivityAssemblyLevel = machineChecked

periodicFivePerturbationInputLevel : ProofLevel
periodicFivePerturbationInputLevel = conditional

periodicFiniteCoerciveInverseInputLevel : ProofLevel
periodicFiniteCoerciveInverseInputLevel = standardImported

periodicBulkGreenKernelInputLevel : ProofLevel
periodicBulkGreenKernelInputLevel = standardImported
