module DASHI.Physics.YangMills.BalabanPeriodicFiniteFourierHodgeCertificate where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteFourierHodgeReduction as Hodge
open import DASHI.Physics.YangMills.BalabanPeriodicBlockSymbolGap

------------------------------------------------------------------------
-- Exact adapter from the periodic symbol package to the existing Hodge
-- reduction. No physical estimate is duplicated here: the low/high block gap
-- and constraint-removal witnesses are consumed once, coherently.
------------------------------------------------------------------------

periodicFiniteFourierHodgeData :
  ∀ {Index State Frequency Bound}
    (symbolData : PeriodicReferenceSymbolData Index State Frequency Bound) →
    (kernelData : PeriodicReferenceKernelData symbolData) →
    (constraints : PeriodicConstraintRemovalData kernelData) →
    (gapData : PeriodicBlockGapData constraints) →
    Hodge.FiniteFourierHodgeData Index State Frequency Bound
periodicFiniteFourierHodgeData symbolData kernelData constraints gapData = record
  { fourier = fourier symbolData
  ; referenceEnergy = referenceEnergy symbolData
  ; normSq = normSq symbolData
  ; frequencyNormSq = frequencyNormSq symbolData
  ; symbolEnergy = symbolEnergy symbolData
  ; scale = scale (ordered symbolData)
  ; LessEqual = LessEqual (ordered symbolData)
  ; Positive = Positive (ordered symbolData)
  ; Nonnegative = Nonnegative (ordered symbolData)
  ; cBulk = cBulk gapData
  ; cBulkPositive = cBulkPositive gapData
  ; GaugeFixedTangent = GaugeFixedTangent constraints
  ; SymbolKernel = SymbolKernel kernelData
  ; ConstantMode = ConstantMode kernelData
  ; SymbolKernelRemoved = SymbolKernelRemoved constraints
  ; finiteFourierDiagonalizesReferenceLaplacian =
      finiteFourierDiagonalizesReferenceLaplacian symbolData
  ; fourierParsevalForBondFields =
      fourierParsevalForBondFields symbolData
  ; referenceSymbolNonnegative =
      referenceSymbolNonnegative symbolData
  ; referenceSymbolKernelCharacterization =
      referenceSymbolKernelCharacterization kernelData
  ; constraintsRemoveReferenceSymbolKernel =
      constraintsRemoveReferenceSymbolKernel constraints
  ; constrainedReferenceSymbolHasPositiveGap =
      constrainedReferenceSymbolHasPositiveGap gapData
  ; CBulkIndependentOfVolume =
      ∀ volume₁ volume₂ spacing scaleValue background →
      cBulkAt gapData volume₁ spacing scaleValue background ≡
      cBulkAt gapData volume₂ spacing scaleValue background
  ; CBulkIndependentOfLatticeSpacing =
      ∀ volume spacing₁ spacing₂ scaleValue background →
      cBulkAt gapData volume spacing₁ scaleValue background ≡
      cBulkAt gapData volume spacing₂ scaleValue background
  ; CBulkIndependentOfScale =
      ∀ volume spacing scale₁ scale₂ background →
      cBulkAt gapData volume spacing scale₁ background ≡
      cBulkAt gapData volume spacing scale₂ background
  ; CBulkUniformOverAdmissibleBackgrounds =
      ∀ volume spacing scaleValue background₁ background₂ →
      cBulkAt gapData volume spacing scaleValue background₁ ≡
      cBulkAt gapData volume spacing scaleValue background₂
  ; cBulkIndependentOfVolume =
      constrainedSymbolGapIndependentOfVolume gapData
  ; cBulkIndependentOfLatticeSpacing =
      constrainedSymbolGapIndependentOfSpacing gapData
  ; cBulkIndependentOfScale =
      constrainedSymbolGapIndependentOfRGScale gapData
  ; cBulkUniformOverAdmissibleBackgrounds =
      constrainedSymbolGapUniformInAdmissibleBackground gapData
  }

periodicBulkGaugeFixedHodgePoincare :
  ∀ {Index State Frequency Bound}
    (symbolData : PeriodicReferenceSymbolData Index State Frequency Bound) →
    (kernelData : PeriodicReferenceKernelData symbolData) →
    (constraints : PeriodicConstraintRemovalData kernelData) →
    (gapData : PeriodicBlockGapData constraints) →
    ∀ index state →
    GaugeFixedTangent constraints index state →
    LessEqual (ordered symbolData)
      (scale (ordered symbolData) (cBulk gapData) (normSq symbolData state))
      (referenceEnergy symbolData index state)
periodicBulkGaugeFixedHodgePoincare symbolData kernelData constraints gapData =
  Hodge.bulkGaugeFixedHodgePoincare
    (periodicFiniteFourierHodgeData
      symbolData kernelData constraints gapData)

periodicUniformBulkHodgeCertificate :
  ∀ {Index State Frequency Bound}
    (symbolData : PeriodicReferenceSymbolData Index State Frequency Bound) →
    (kernelData : PeriodicReferenceKernelData symbolData) →
    (constraints : PeriodicConstraintRemovalData kernelData) →
    (gapData : PeriodicBlockGapData constraints) →
    Hodge.UniformBulkHodgeCertificate Index State Bound
periodicUniformBulkHodgeCertificate symbolData kernelData constraints gapData =
  Hodge.finiteFourierHodgeCertificate
    (periodicFiniteFourierHodgeData
      symbolData kernelData constraints gapData)

periodicFiniteFourierHodgeAdapterLevel : ProofLevel
periodicFiniteFourierHodgeAdapterLevel = machineChecked

periodicPhysicalLocalBlockGapLevel : ProofLevel
periodicPhysicalLocalBlockGapLevel = conditional
