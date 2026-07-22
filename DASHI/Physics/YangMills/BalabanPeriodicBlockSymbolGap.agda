module DASHI.Physics.YangMills.BalabanPeriodicBlockSymbolGap where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier

------------------------------------------------------------------------
-- Order-theoretic and kernel part of the periodic reference-symbol gap.
--
-- The module separates standard finite Fourier/trigonometric facts from the
-- genuinely model-specific local-block estimate. Given the exact three-square
-- decomposition, component nonnegativity, kernel identification, constraint
-- removal, and a low/high frequency split, the positive uniform gap is derived
-- by ordinary case analysis and transitivity.
------------------------------------------------------------------------

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

record Both (A B : Set) : Set where
  constructor both
  field
    firstProof : A
    secondProof : B

open Both public

record Iff (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

open Iff public

record OrderedAdditiveBound (Bound : Set) : Set₁ where
  field
    zero : Bound
    add scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    Positive Nonnegative : Bound → Set

    lessEqualTransitive : ∀ {a b c} →
      LessEqual a b → LessEqual b c → LessEqual a c

    addNonnegative : ∀ {a b} →
      Nonnegative a → Nonnegative b → Nonnegative (add a b)

open OrderedAdditiveBound public

record PeriodicReferenceSymbolData
    (Index State Frequency Bound : Set) : Set₁ where
  field
    ordered : OrderedAdditiveBound Bound

    fourier : State → Frequency
    referenceEnergy : Index → State → Bound
    normSq : State → Bound
    frequencyNormSq : Frequency → Bound

    differenceSymbolEnergy gaugeSymbolEnergy blockSymbolEnergy :
      Index → Frequency → Bound
    symbolEnergy : Index → Frequency → Bound

    referenceSymbolSumOfSquares : ∀ index frequency →
      symbolEnergy index frequency ≡
      add ordered
        (differenceSymbolEnergy index frequency)
        (add ordered
          (gaugeSymbolEnergy index frequency)
          (blockSymbolEnergy index frequency))

    differenceSymbolNonnegative : ∀ index frequency →
      Nonnegative ordered (differenceSymbolEnergy index frequency)
    gaugeSymbolNonnegative : ∀ index frequency →
      Nonnegative ordered (gaugeSymbolEnergy index frequency)
    blockSymbolNonnegative : ∀ index frequency →
      Nonnegative ordered (blockSymbolEnergy index frequency)

    finiteFourierDiagonalizesReferenceLaplacian : ∀ index state →
      referenceEnergy index state ≡ symbolEnergy index (fourier state)

    fourierParsevalForBondFields : ∀ state →
      normSq state ≡ frequencyNormSq (fourier state)

open PeriodicReferenceSymbolData public

referenceSymbolNonnegative :
  ∀ {Index State Frequency Bound}
    (dataSet : PeriodicReferenceSymbolData Index State Frequency Bound) →
  ∀ index frequency →
  Nonnegative (ordered dataSet) (symbolEnergy dataSet index frequency)
referenceSymbolNonnegative dataSet index frequency
  rewrite referenceSymbolSumOfSquares dataSet index frequency =
  addNonnegative (ordered dataSet)
    (differenceSymbolNonnegative dataSet index frequency)
    (addNonnegative (ordered dataSet)
      (gaugeSymbolNonnegative dataSet index frequency)
      (blockSymbolNonnegative dataSet index frequency))

record PeriodicReferenceKernelData
    {Index State Frequency Bound : Set}
    (symbolData : PeriodicReferenceSymbolData Index State Frequency Bound) : Set₁ where
  field
    ZeroMomentum : Frequency → Set
    DifferenceSymbolZero : Index → Frequency → Set
    SymbolKernel : Index → Frequency → Set
    ConstantMode : Frequency → Set

    zeroMomentumImpliesDifferenceSymbolZero : ∀ index frequency →
      ZeroMomentum frequency → DifferenceSymbolZero index frequency

    differenceSymbolZeroImpliesZeroMomentum : ∀ index frequency →
      DifferenceSymbolZero index frequency → ZeroMomentum frequency

    referenceSymbolZeroImpliesConstantMode : ∀ index frequency →
      SymbolKernel index frequency → ConstantMode frequency

    constantModeImpliesReferenceSymbolZero : ∀ index frequency →
      ConstantMode frequency → SymbolKernel index frequency

    ForwardDifferenceSymbolNormSq : Index → Frequency → Set
    forwardDifferenceSymbolNormSq : ∀ index frequency →
      ForwardDifferenceSymbolNormSq index frequency

open PeriodicReferenceKernelData public

referenceSymbolKernelIffConstantMode :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound} →
  (kernelData : PeriodicReferenceKernelData symbolData) →
  ∀ index frequency →
  Iff
    (SymbolKernel kernelData index frequency)
    (ConstantMode kernelData frequency)
referenceSymbolKernelIffConstantMode kernelData index frequency =
  iff
    (referenceSymbolZeroImpliesConstantMode kernelData index frequency)
    (constantModeImpliesReferenceSymbolZero kernelData index frequency)

referenceSymbolKernelCharacterization :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound} →
  (kernelData : PeriodicReferenceKernelData symbolData) →
  ∀ index frequency →
  SymbolKernel kernelData index frequency →
  ConstantMode kernelData frequency
referenceSymbolKernelCharacterization = referenceSymbolZeroImpliesConstantMode

------------------------------------------------------------------------
-- Constraint identities and exact removal of the reference-symbol kernel.
------------------------------------------------------------------------

record PeriodicConstraintRemovalData
    {Index State Frequency Bound : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    (kernelData : PeriodicReferenceKernelData symbolData) : Set₁ where
  field
    GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
      BoundaryCompatible : Index → State → Set

    GaugeFixedTangent : Index → State → Set

    tangentGaugeOrthogonal : ∀ index state →
      GaugeFixedTangent index state → GaugeOrthogonal index state
    tangentBlockAverageZero : ∀ index state →
      GaugeFixedTangent index state → BlockAverageZero index state
    tangentResidualGaugeOrthogonal : ∀ index state →
      GaugeFixedTangent index state → ResidualGaugeOrthogonal index state
    tangentBoundaryCompatible : ∀ index state →
      GaugeFixedTangent index state → BoundaryCompatible index state

    GaugeOrthogonalityFourierIdentity BlockAverageZeroFourierIdentity
      ResidualGaugeOrthogonalityFourierIdentity
      BoundaryCompatibilityFourierIdentity : Index → State → Set

    gaugeOrthogonalityFourierIdentity : ∀ index state →
      GaugeOrthogonal index state →
      GaugeOrthogonalityFourierIdentity index state
    blockAverageZeroFourierIdentity : ∀ index state →
      BlockAverageZero index state →
      BlockAverageZeroFourierIdentity index state
    residualGaugeOrthogonalityFourierIdentity : ∀ index state →
      ResidualGaugeOrthogonal index state →
      ResidualGaugeOrthogonalityFourierIdentity index state
    boundaryCompatibilityFourierIdentity : ∀ index state →
      BoundaryCompatible index state →
      BoundaryCompatibilityFourierIdentity index state

    ExactMode ResidualKernel BoundaryKernel : Index → Frequency → Set

    gaugeConstraintRemovesExactModes : ∀ index state →
      GaugeOrthogonal index state →
      ExactMode index (fourier symbolData state) → Empty

    blockConstraintRemovesConstantModes : ∀ index state →
      BlockAverageZero index state →
      ConstantMode kernelData (fourier symbolData state) → Empty

    residualGaugeConstraintRemovesResidualKernel : ∀ index state →
      ResidualGaugeOrthogonal index state →
      ResidualKernel index (fourier symbolData state) → Empty

    boundaryConstraintRemovesBoundaryKernel : ∀ index state →
      BoundaryCompatible index state →
      BoundaryKernel index (fourier symbolData state) → Empty

    -- Every literal reference-symbol kernel vector is classified into exactly
    -- one of the four mechanisms removed by the physical constraints.
    symbolKernelClassification : ∀ index frequency →
      SymbolKernel kernelData index frequency →
      Either
        (ExactMode index frequency)
        (Either
          (ConstantMode kernelData frequency)
          (Either
            (ResidualKernel index frequency)
            (BoundaryKernel index frequency)))

open PeriodicConstraintRemovalData public

SymbolKernelRemoved :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData} →
  PeriodicConstraintRemovalData kernelData → Index → Frequency → Set
SymbolKernelRemoved {kernelData = kernelData} constraints index frequency =
  Not (SymbolKernel kernelData index frequency)

combinedConstraintsRemoveSymbolKernel :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData} →
  (constraints : PeriodicConstraintRemovalData kernelData) →
  ∀ index state →
  GaugeOrthogonal constraints index state →
  BlockAverageZero constraints index state →
  ResidualGaugeOrthogonal constraints index state →
  BoundaryCompatible constraints index state →
  SymbolKernelRemoved constraints index (fourier symbolData state)
combinedConstraintsRemoveSymbolKernel {symbolData = symbolData}
  constraints index state gauge block residual boundary kernel
  with symbolKernelClassification constraints index (fourier symbolData state) kernel
... | left exactMode =
  gaugeConstraintRemovesExactModes constraints index state gauge exactMode
... | right (left constantMode) =
  blockConstraintRemovesConstantModes constraints index state block constantMode
... | right (right (left residualMode)) =
  residualGaugeConstraintRemovesResidualKernel constraints index state residual residualMode
... | right (right (right boundaryMode)) =
  boundaryConstraintRemovesBoundaryKernel constraints index state boundary boundaryMode

constraintsRemoveReferenceSymbolKernel :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData} →
  (constraints : PeriodicConstraintRemovalData kernelData) →
  ∀ index state →
  GaugeFixedTangent constraints index state →
  SymbolKernelRemoved constraints index (fourier symbolData state)
constraintsRemoveReferenceSymbolKernel constraints index state tangent =
  combinedConstraintsRemoveSymbolKernel constraints index state
    (tangentGaugeOrthogonal constraints index state tangent)
    (tangentBlockAverageZero constraints index state tangent)
    (tangentResidualGaugeOrthogonal constraints index state tangent)
    (tangentBoundaryCompatible constraints index state tangent)

------------------------------------------------------------------------
-- Uniform low/high symbol gap.
------------------------------------------------------------------------

record PeriodicBlockGapData
    {Index State Frequency Bound : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    (constraints : PeriodicConstraintRemovalData kernelData) : Set₁ where
  field
    cBulk : Bound
    cBulkPositive : Positive (ordered symbolData) cBulk

    -- The selected gap constant is a function only of fixed blocking/group
    -- data. The indexed presentation makes all uniformity claims equality-valued.
    Volume LatticeSpacing RGScale Background : Set
    cBulkAt : Volume → LatticeSpacing → RGScale → Background → Bound
    cBulkAtEqualsSelected : ∀ volume spacing scaleValue background →
      cBulkAt volume spacing scaleValue background ≡ cBulk

    LowMomentum HighMomentum : Index → Frequency → Set
    blockZeroModeFrequencyDecomposition : ∀ index frequency →
      Either (LowMomentum index frequency) (HighMomentum index frequency)

    nonzeroMomentumDifferenceSymbolLowerBound : ∀ index frequency →
      HighMomentum index frequency →
      LessEqual (ordered symbolData)
        (scale (ordered symbolData) cBulk
          (frequencyNormSq symbolData frequency))
        (differenceSymbolEnergy symbolData index frequency)

    lowMomentumControlledByBlockConstraint : ∀ index frequency →
      LowMomentum index frequency →
      SymbolKernelRemoved constraints index frequency →
      LessEqual (ordered symbolData)
        (scale (ordered symbolData) cBulk
          (frequencyNormSq symbolData frequency))
        (symbolEnergy symbolData index frequency)

    highMomentumControlledByDifferenceSymbol : ∀ index frequency →
      HighMomentum index frequency →
      LessEqual (ordered symbolData)
        (differenceSymbolEnergy symbolData index frequency)
        (symbolEnergy symbolData index frequency)

    GaugeLongitudinalModeControlled TransverseModeControlledByCurl :
      Index → Frequency → Set
    gaugeLongitudinalModeControlled : ∀ index frequency →
      GaugeLongitudinalModeControlled index frequency
    transverseModeControlledByCurl : ∀ index frequency →
      TransverseModeControlledByCurl index frequency

open PeriodicBlockGapData public

constrainedSymbolPointwiseLowerBound :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
  (gapData : PeriodicBlockGapData constraints) →
  ∀ index frequency →
  SymbolKernelRemoved constraints index frequency →
  LessEqual (ordered symbolData)
    (scale (ordered symbolData) (cBulk gapData)
      (frequencyNormSq symbolData frequency))
    (symbolEnergy symbolData index frequency)
constrainedSymbolPointwiseLowerBound {symbolData = symbolData}
  gapData index frequency removed
  with blockZeroModeFrequencyDecomposition gapData index frequency
... | left low =
  lowMomentumControlledByBlockConstraint gapData index frequency low removed
... | right high =
  lessEqualTransitive (ordered symbolData)
    (nonzeroMomentumDifferenceSymbolLowerBound gapData index frequency high)
    (highMomentumControlledByDifferenceSymbol gapData index frequency high)

constrainedReferenceSymbolHasPositiveGap :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
  (gapData : PeriodicBlockGapData constraints) →
  ∀ index frequency →
  SymbolKernelRemoved constraints index frequency →
  LessEqual (ordered symbolData)
    (scale (ordered symbolData) (cBulk gapData)
      (frequencyNormSq symbolData frequency))
    (symbolEnergy symbolData index frequency)
constrainedReferenceSymbolHasPositiveGap = constrainedSymbolPointwiseLowerBound

explicitCBulkDefinition :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
  PeriodicBlockGapData constraints → Bound
explicitCBulkDefinition = cBulk

equalitySymmetric : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
equalitySymmetric refl = refl

equalityTransitive : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
equalityTransitive refl refl = refl

constrainedSymbolGapIndependentOfVolume :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
  (gapData : PeriodicBlockGapData constraints) →
  ∀ volume₁ volume₂ spacing scaleValue background →
  cBulkAt gapData volume₁ spacing scaleValue background ≡
  cBulkAt gapData volume₂ spacing scaleValue background
constrainedSymbolGapIndependentOfVolume gapData volume₁ volume₂ spacing scaleValue background =
  equalityTransitive
    (cBulkAtEqualsSelected gapData volume₁ spacing scaleValue background)
    (equalitySymmetric
      (cBulkAtEqualsSelected gapData volume₂ spacing scaleValue background))

constrainedSymbolGapIndependentOfSpacing :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
  (gapData : PeriodicBlockGapData constraints) →
  ∀ volume spacing₁ spacing₂ scaleValue background →
  cBulkAt gapData volume spacing₁ scaleValue background ≡
  cBulkAt gapData volume spacing₂ scaleValue background
constrainedSymbolGapIndependentOfSpacing gapData volume spacing₁ spacing₂ scaleValue background =
  equalityTransitive
    (cBulkAtEqualsSelected gapData volume spacing₁ scaleValue background)
    (equalitySymmetric
      (cBulkAtEqualsSelected gapData volume spacing₂ scaleValue background))

constrainedSymbolGapIndependentOfRGScale :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
  (gapData : PeriodicBlockGapData constraints) →
  ∀ volume spacing scale₁ scale₂ background →
  cBulkAt gapData volume spacing scale₁ background ≡
  cBulkAt gapData volume spacing scale₂ background
constrainedSymbolGapIndependentOfRGScale gapData volume spacing scale₁ scale₂ background =
  equalityTransitive
    (cBulkAtEqualsSelected gapData volume spacing scale₁ background)
    (equalitySymmetric
      (cBulkAtEqualsSelected gapData volume spacing scale₂ background))

constrainedSymbolGapUniformInAdmissibleBackground :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
  (gapData : PeriodicBlockGapData constraints) →
  ∀ volume spacing scaleValue background₁ background₂ →
  cBulkAt gapData volume spacing scaleValue background₁ ≡
  cBulkAt gapData volume spacing scaleValue background₂
constrainedSymbolGapUniformInAdmissibleBackground gapData volume spacing scaleValue background₁ background₂ =
  equalityTransitive
    (cBulkAtEqualsSelected gapData volume spacing scaleValue background₁)
    (equalitySymmetric
      (cBulkAtEqualsSelected gapData volume spacing scaleValue background₂))

localBlockZeroGivesBlockScaleGap :
  ∀ {Index State Frequency Bound}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
  (gapData : PeriodicBlockGapData constraints) →
  ∀ index frequency →
  LowMomentum gapData index frequency →
  SymbolKernelRemoved constraints index frequency →
  LessEqual (ordered symbolData)
    (scale (ordered symbolData) (cBulk gapData)
      (frequencyNormSq symbolData frequency))
    (symbolEnergy symbolData index frequency)
localBlockZeroGivesBlockScaleGap = lowMomentumControlledByBlockConstraint

------------------------------------------------------------------------
-- The ordinary global mean-zero estimate is not volume-uniform.
------------------------------------------------------------------------

record MeanZeroGapCounterexample
    (Volume State Bound : Set)
    (MeanZero : Volume → State → Set)
    (normSq : State → Bound)
    (gradientEnergy : Volume → State → Bound)
    (scale : Bound → Bound → Bound)
    (LessEqual : Bound → Bound → Set)
    (c : Bound) : Set₁ where
  field
    volume : Volume
    state : State
    meanZero : MeanZero volume state
    violates : Not
      (LessEqual
        (scale c (normSq state))
        (gradientEnergy volume state))

open MeanZeroGapCounterexample public

record GlobalMeanZeroNoUniformGapAuthority (Volume State Bound : Set) : Set₁ where
  field
    Positive : Bound → Set
    MeanZero : Volume → State → Set
    normSq : State → Bound
    gradientEnergy : Volume → State → Bound
    scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    globalMeanZeroDoesNotGiveVolumeUniformGap : ∀ c →
      Positive c →
      MeanZeroGapCounterexample
        Volume State Bound MeanZero normSq gradientEnergy scale LessEqual c

open GlobalMeanZeroNoUniformGapAuthority public

periodicReferenceSymbolAssemblyLevel : ProofLevel
periodicReferenceSymbolAssemblyLevel = machineChecked

periodicCharacterAndTrigonometricKernelFactsLevel : ProofLevel
periodicCharacterAndTrigonometricKernelFactsLevel = standardImported

localBlockGapInputLevel : ProofLevel
localBlockGapInputLevel = conditional

constrainedSymbolGapAssemblyLevel : ProofLevel
constrainedSymbolGapAssemblyLevel = machineChecked

globalMeanZeroCounterexampleLevel : ProofLevel
globalMeanZeroCounterexampleLevel = standardImported
