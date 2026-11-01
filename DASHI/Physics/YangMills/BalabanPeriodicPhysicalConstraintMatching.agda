module DASHI.Physics.YangMills.BalabanPeriodicPhysicalConstraintMatching where

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (Empty)
open import DASHI.Physics.YangMills.BalabanPeriodicBlockSymbolGap
import DASHI.Physics.YangMills.BalabanBulkPropagatorAnalyticInhabitation as Bulk

------------------------------------------------------------------------
-- Exact physical-constraint adapter.
--
-- The generic periodic symbol module deliberately does not identify its
-- `GaugeFixedTangent` with the finite-background tangent used by the rest of
-- DASHI.  This module makes that identification definitionally: the tangent is
-- the four-field record consisting of gauge orthogonality, local block-average
-- zero, residual gauge orthogonality and boundary compatibility.
--
-- The genuinely analytic Fourier identities and mode-exclusion statements are
-- retained as proof-relevant inputs.  Once supplied for the literal operators,
-- every projection from the physical tangent and the final kernel-removal
-- theorem are machine checked here.
------------------------------------------------------------------------

record PhysicalConstraintFourierInputs
    {Index State Frequency Bound : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    (kernelData : PeriodicReferenceKernelData symbolData)
    (GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
      BoundaryCompatible : Index → State → Set) : Set₁ where
  field
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

    symbolKernelClassification : ∀ index frequency →
      SymbolKernel kernelData index frequency →
      Either
        (ExactMode index frequency)
        (Either
          (ConstantMode kernelData frequency)
          (Either
            (ResidualKernel index frequency)
            (BoundaryKernel index frequency)))

open PhysicalConstraintFourierInputs public

physicalConstraintRemovalData :
  ∀ {Index State Frequency Bound : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    (kernelData : PeriodicReferenceKernelData symbolData)
    (GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
      BoundaryCompatible : Index → State → Set) →
    PhysicalConstraintFourierInputs kernelData
      GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
      BoundaryCompatible →
    PeriodicConstraintRemovalData kernelData
physicalConstraintRemovalData kernelData
  GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
  BoundaryCompatible inputs = record
  { GaugeOrthogonal = GaugeOrthogonal
  ; BlockAverageZero = BlockAverageZero
  ; ResidualGaugeOrthogonal = ResidualGaugeOrthogonal
  ; BoundaryCompatible = BoundaryCompatible
  ; GaugeFixedTangent =
      Bulk.ConcreteGaugeFixedTangent
        GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
        BoundaryCompatible
  ; tangentGaugeOrthogonal = λ index state tangent →
      Bulk.gaugeOrthogonal tangent
  ; tangentBlockAverageZero = λ index state tangent →
      Bulk.blockAverageZero tangent
  ; tangentResidualGaugeOrthogonal = λ index state tangent →
      Bulk.residualGaugeOrthogonal tangent
  ; tangentBoundaryCompatible = λ index state tangent →
      Bulk.boundaryCompatible tangent
  ; GaugeOrthogonalityFourierIdentity =
      GaugeOrthogonalityFourierIdentity inputs
  ; BlockAverageZeroFourierIdentity =
      BlockAverageZeroFourierIdentity inputs
  ; ResidualGaugeOrthogonalityFourierIdentity =
      ResidualGaugeOrthogonalityFourierIdentity inputs
  ; BoundaryCompatibilityFourierIdentity =
      BoundaryCompatibilityFourierIdentity inputs
  ; gaugeOrthogonalityFourierIdentity =
      gaugeOrthogonalityFourierIdentity inputs
  ; blockAverageZeroFourierIdentity =
      blockAverageZeroFourierIdentity inputs
  ; residualGaugeOrthogonalityFourierIdentity =
      residualGaugeOrthogonalityFourierIdentity inputs
  ; boundaryCompatibilityFourierIdentity =
      boundaryCompatibilityFourierIdentity inputs
  ; ExactMode = ExactMode inputs
  ; ResidualKernel = ResidualKernel inputs
  ; BoundaryKernel = BoundaryKernel inputs
  ; gaugeConstraintRemovesExactModes =
      gaugeConstraintRemovesExactModes inputs
  ; blockConstraintRemovesConstantModes =
      blockConstraintRemovesConstantModes inputs
  ; residualGaugeConstraintRemovesResidualKernel =
      residualGaugeConstraintRemovesResidualKernel inputs
  ; boundaryConstraintRemovesBoundaryKernel =
      boundaryConstraintRemovesBoundaryKernel inputs
  ; symbolKernelClassification = symbolKernelClassification inputs
  }

physicalGaugeFixedTangentRemovesReferenceKernel :
  ∀ {Index State Frequency Bound : Set}
    {symbolData : PeriodicReferenceSymbolData Index State Frequency Bound}
    (kernelData : PeriodicReferenceKernelData symbolData)
    (GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
      BoundaryCompatible : Index → State → Set)
    (inputs : PhysicalConstraintFourierInputs kernelData
      GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
      BoundaryCompatible) →
    ∀ index state →
    Bulk.ConcreteGaugeFixedTangent
      GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
      BoundaryCompatible index state →
    SymbolKernelRemoved
      (physicalConstraintRemovalData kernelData
        GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
        BoundaryCompatible inputs)
      index (fourier symbolData state)
physicalGaugeFixedTangentRemovesReferenceKernel kernelData
  GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
  BoundaryCompatible inputs =
  constraintsRemoveReferenceSymbolKernel
    (physicalConstraintRemovalData kernelData
      GaugeOrthogonal BlockAverageZero ResidualGaugeOrthogonal
      BoundaryCompatible inputs)

periodicPhysicalConstraintAdapterLevel : ProofLevel
periodicPhysicalConstraintAdapterLevel = machineChecked

periodicPhysicalConstraintFourierInputLevel : ProofLevel
periodicPhysicalConstraintFourierInputLevel = conditional
