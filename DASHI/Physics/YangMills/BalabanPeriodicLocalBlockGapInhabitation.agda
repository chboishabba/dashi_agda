module DASHI.Physics.YangMills.BalabanPeriodicLocalBlockGapInhabitation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicBlockSymbolGap

------------------------------------------------------------------------
-- Physical low/high-frequency inhabitation of the periodic block gap.
--
-- The previous generic module accepted an already assembled
-- `PeriodicBlockGapData`.  Here the owner is split at the mathematically useful
-- boundary:
--
--   * the high-frequency estimate is the standard trigonometric lower bound
--     for the literal forward-difference multiplier;
--   * the low-frequency estimate is the model-specific local block Poincare
--     theorem, after the exact physical constraints have removed the kernel.
--
-- Uniformity of the selected cBulk is no longer an independent proof field: the
-- indexed constant is definitionally constant in volume, spacing, RG scale and
-- admissible background.
------------------------------------------------------------------------

record PhysicalLocalBlockGapInputs
    {Index State Frequency Bound : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    (constraints : PeriodicConstraintRemovalData kernelData) : Set₁ where
  field
    cBulk : Bound
    cBulkPositive : Positive (ordered symbolData) cBulk

    Volume LatticeSpacing RGScale Background : Set

    LowMomentum HighMomentum : Index → Frequency → Set
    blockZeroModeFrequencyDecomposition : ∀ index frequency →
      Either (LowMomentum index frequency) (HighMomentum index frequency)

    -- Standard finite-lattice trigonometric estimate.
    nonzeroMomentumDifferenceSymbolLowerBound : ∀ index frequency →
      HighMomentum index frequency →
      LessEqual (ordered symbolData)
        (scale (ordered symbolData) cBulk
          (frequencyNormSq symbolData frequency))
        (differenceSymbolEnergy symbolData index frequency)

    -- The genuinely physical block-local estimate.
    lowMomentumControlledByLocalBlockConstraint : ∀ index frequency →
      LowMomentum index frequency →
      SymbolKernelRemoved constraints index frequency →
      LessEqual (ordered symbolData)
        (scale (ordered symbolData) cBulk
          (frequencyNormSq symbolData frequency))
        (symbolEnergy symbolData index frequency)

    highMomentumDifferenceEnergyBelowReference : ∀ index frequency →
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

open PhysicalLocalBlockGapInputs public

physicalPeriodicBlockGapData :
  ∀ {Index State Frequency Bound : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
    PhysicalLocalBlockGapInputs constraints →
    PeriodicBlockGapData constraints
physicalPeriodicBlockGapData {constraints = constraints} inputs = record
  { cBulk = cBulk inputs
  ; cBulkPositive = cBulkPositive inputs
  ; Volume = Volume inputs
  ; LatticeSpacing = LatticeSpacing inputs
  ; RGScale = RGScale inputs
  ; Background = Background inputs
  ; cBulkAt = λ volume spacing scaleValue background → cBulk inputs
  ; cBulkAtEqualsSelected = λ volume spacing scaleValue background → refl
  ; LowMomentum = LowMomentum inputs
  ; HighMomentum = HighMomentum inputs
  ; blockZeroModeFrequencyDecomposition =
      blockZeroModeFrequencyDecomposition inputs
  ; nonzeroMomentumDifferenceSymbolLowerBound =
      nonzeroMomentumDifferenceSymbolLowerBound inputs
  ; lowMomentumControlledByBlockConstraint =
      lowMomentumControlledByLocalBlockConstraint inputs
  ; highMomentumControlledByDifferenceSymbol =
      highMomentumDifferenceEnergyBelowReference inputs
  ; GaugeLongitudinalModeControlled =
      GaugeLongitudinalModeControlled inputs
  ; TransverseModeControlledByCurl =
      TransverseModeControlledByCurl inputs
  ; gaugeLongitudinalModeControlled =
      gaugeLongitudinalModeControlled inputs
  ; transverseModeControlledByCurl =
      transverseModeControlledByCurl inputs
  }

physicalLocalBlockGapImpliesUniformReferenceGap :
  ∀ {Index State Frequency Bound : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
    (inputs : PhysicalLocalBlockGapInputs constraints) →
    ∀ index frequency →
    SymbolKernelRemoved constraints index frequency →
    LessEqual (ordered symbolData)
      (scale (ordered symbolData) (cBulk inputs)
        (frequencyNormSq symbolData frequency))
      (symbolEnergy symbolData index frequency)
physicalLocalBlockGapImpliesUniformReferenceGap inputs =
  constrainedReferenceSymbolHasPositiveGap
    (physicalPeriodicBlockGapData inputs)

physicalCBulkIndependentOfVolume :
  ∀ {Index State Frequency Bound : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
    (inputs : PhysicalLocalBlockGapInputs constraints) →
    ∀ volume₁ volume₂ spacing scaleValue background →
    cBulkAt (physicalPeriodicBlockGapData inputs)
      volume₁ spacing scaleValue background
    ≡ cBulkAt (physicalPeriodicBlockGapData inputs)
      volume₂ spacing scaleValue background
physicalCBulkIndependentOfVolume inputs =
  constrainedSymbolGapIndependentOfVolume
    (physicalPeriodicBlockGapData inputs)

physicalCBulkIndependentOfSpacing :
  ∀ {Index State Frequency Bound : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
    (inputs : PhysicalLocalBlockGapInputs constraints) →
    ∀ volume spacing₁ spacing₂ scaleValue background →
    cBulkAt (physicalPeriodicBlockGapData inputs)
      volume spacing₁ scaleValue background
    ≡ cBulkAt (physicalPeriodicBlockGapData inputs)
      volume spacing₂ scaleValue background
physicalCBulkIndependentOfSpacing inputs =
  constrainedSymbolGapIndependentOfSpacing
    (physicalPeriodicBlockGapData inputs)

physicalCBulkIndependentOfRGScale :
  ∀ {Index State Frequency Bound : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
    (inputs : PhysicalLocalBlockGapInputs constraints) →
    ∀ volume spacing scale₁ scale₂ background →
    cBulkAt (physicalPeriodicBlockGapData inputs)
      volume spacing scale₁ background
    ≡ cBulkAt (physicalPeriodicBlockGapData inputs)
      volume spacing scale₂ background
physicalCBulkIndependentOfRGScale inputs =
  constrainedSymbolGapIndependentOfRGScale
    (physicalPeriodicBlockGapData inputs)

physicalCBulkUniformInBackground :
  ∀ {Index State Frequency Bound : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    {kernelData : PeriodicReferenceKernelData symbolData}
    {constraints : PeriodicConstraintRemovalData kernelData} →
    (inputs : PhysicalLocalBlockGapInputs constraints) →
    ∀ volume spacing scaleValue background₁ background₂ →
    cBulkAt (physicalPeriodicBlockGapData inputs)
      volume spacing scaleValue background₁
    ≡ cBulkAt (physicalPeriodicBlockGapData inputs)
      volume spacing scaleValue background₂
physicalCBulkUniformInBackground inputs =
  constrainedSymbolGapUniformInAdmissibleBackground
    (physicalPeriodicBlockGapData inputs)

periodicLocalBlockGapAssemblyLevel : ProofLevel
periodicLocalBlockGapAssemblyLevel = machineChecked

periodicHighFrequencyTrigonometricInputLevel : ProofLevel
periodicHighFrequencyTrigonometricInputLevel = standardImported

periodicLowFrequencyLocalBlockPoincareInputLevel : ProofLevel
periodicLowFrequencyLocalBlockPoincareInputLevel = conditional
