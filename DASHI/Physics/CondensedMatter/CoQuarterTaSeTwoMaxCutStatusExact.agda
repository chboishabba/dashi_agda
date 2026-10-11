module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoMaxCutStatusExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoBNS194268SameObjectExact as BNS
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoBlochRepresentationBoundaryExact as Bloch
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoPublishedMaterialProducerExact as Material
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoARPESWitnessGateExact as ARPES

record CoQuarterTaSeTwoMaxCutStatus : Set where
  constructor co-quarter-tase-two-max-cut-status
  field
    bnsMetadataFixed : Bool
    independentOperationEqualityClosed : Bool
    literalBNSConsumedByBlochReceipt : Bool
    blochPhaseImplemented : Bool
    sewingCocycleExecutionClosed : Bool
    publishedCrystalBasisFixed : Bool
    publishedDFTRecipeFixed : Bool
    materialHamiltonianClosed : Bool
    rawARPESPayloadPresent : Bool
    exactSpectralObserverClosed : Bool
    quantitativeFitClosed : Bool
    umbrellaIntegrated : Bool

canonicalCoQuarterTaSeTwoMaxCutStatus : CoQuarterTaSeTwoMaxCutStatus
canonicalCoQuarterTaSeTwoMaxCutStatus =
  co-quarter-tase-two-max-cut-status
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    true

existingBNSStatus : BNS.OperationSameObjectStatus
existingBNSStatus = BNS.canonicalOperationSameObjectStatus

existingBlochStatus : Bloch.BlochSewingContract
existingBlochStatus = Bloch.canonicalBlochSewingContract

existingMaterialProducerStatus : Material.MaterialHamiltonianProducerStatus
existingMaterialProducerStatus = Material.canonicalMaterialHamiltonianProducerStatus

existingARPESStatus : ARPES.CoARPESAcquisitionStatus
existingARPESStatus = ARPES.canonicalCoARPESAcquisitionStatus

record IrreduciblePhysicalResidual : Set where
  constructor irreducible-physical-residual
  field
    exactElectronicStructureArtifactNeeded : Bool
    materialSOCExchangeHamiltonianNeeded : Bool
    rawSpinARPESPayloadNeeded : Bool
    calibratedSpectralObserverNeeded : Bool
    quantitativeForwardFitNeeded : Bool
    furtherAbstractToyLayerNeeded : Bool

canonicalIrreduciblePhysicalResidual : IrreduciblePhysicalResidual
canonicalIrreduciblePhysicalResidual =
  irreducible-physical-residual true true true true true false
