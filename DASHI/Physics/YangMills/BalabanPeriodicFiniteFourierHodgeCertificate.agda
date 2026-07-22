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
  { Hodge.fourier = fourier symbolData
  ; Hodge.referenceEnergy = referenceEnergy symbolData
  ; Hodge.normSq = normSq symbolData
  ; Hodge.frequencyNormSq = frequencyNormSq symbolData
  ; Hodge.symbolEnergy = symbolEnergy symbolData
  ; Hodge.scale = scale (ordered symbolData)
  ; Hodge.LessEqual = LessEqual (ordered symbolData)
  ; Hodge.Positive = Positive (ordered symbolData)
  ; Hodge.Nonnegative = Nonnegative (ordered symbolData)
  ; Hodge.cBulk = cBulk gapData
  ; Hodge.cBulkPositive = cBulkPositive gapData
  ; Hodge.GaugeFixedTangent = GaugeFixedTangent constraints
  ; Hodge.SymbolKernel = SymbolKernel kernelData
  ; Hodge.ConstantMode = ConstantMode kernelData
  ; Hodge.SymbolKernelRemoved = SymbolKernelRemoved constraints
  ; Hodge.finiteFourierDiagonalizesReferenceLaplacian =
      finiteFourierDiagonalizesReferenceLaplacian symbolData
  ; Hodge.fourierParsevalForBondFields =
      fourierParsevalForBondFields symbolData
  ; Hodge.referenceSymbolNonnegative =
      referenceSymbolNonnegative symbolData
  ; Hodge.referenceSymbolKernelCharacterization =
      referenceSymbolKernelCharacterization kernelData
  ; Hodge.constraintsRemoveReferenceSymbolKernel =
      constraintsRemoveReferenceSymbolKernel constraints
  ; Hodge.constrainedReferenceSymbolHasPositiveGap =
      constrainedReferenceSymbolHasPositiveGap gapData
  ; Hodge.CBulkIndependentOfVolume =
      ∀ volume₁ volume₂ spacing scaleValue background →
      cBulkAt gapData volume₁ spacing scaleValue background ≡
      cBulkAt gapData volume₂ spacing scaleValue background
  ; Hodge.CBulkIndependentOfLatticeSpacing =
      ∀ volume spacing₁ spacing₂ scaleValue background →
      cBulkAt gapData volume spacing₁ scaleValue background ≡
      cBulkAt gapData volume spacing₂ scaleValue background
  ; Hodge.CBulkIndependentOfScale =
      ∀ volume spacing scale₁ scale₂ background →
      cBulkAt gapData volume spacing scale₁ background ≡
      cBulkAt gapData volume spacing scale₂ background
  ; Hodge.CBulkUniformOverAdmissibleBackgrounds =
      ∀ volume spacing scaleValue background₁ background₂ →
      cBulkAt gapData volume spacing scaleValue background₁ ≡
      cBulkAt gapData volume spacing scaleValue background₂
  ; Hodge.cBulkIndependentOfVolume =
      constrainedSymbolGapIndependentOfVolume gapData
  ; Hodge.cBulkIndependentOfLatticeSpacing =
      constrainedSymbolGapIndependentOfSpacing gapData
  ; Hodge.cBulkIndependentOfScale =
      constrainedSymbolGapIndependentOfRGScale gapData
  ; Hodge.cBulkUniformOverAdmissibleBackgrounds =
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
