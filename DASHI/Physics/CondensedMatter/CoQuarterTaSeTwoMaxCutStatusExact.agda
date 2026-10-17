module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoMaxCutStatusExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoBNS194268SameObjectExact as BNS
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoBlochRepresentationBoundaryExact as Bloch
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoPublishedMaterialProducerExact as Material
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoWannierSpectralProducerExact as Wannier
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoWannierBNSCovarianceExact as WannierBNS
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoWannier3DResponseExact as Response3D
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoNonAbelianTopologyExact as Topology
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoPublishedARPESConstraintsExact as PublishedARPES
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoKzCalibrationCrossPollinationExact as Kz
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoIndependentTheoryCrossValidationExact as Independent
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoSpinSpaceGeneratorBridgeExact as SpinSpace
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoARPESWitnessGateExact as ARPES
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoARPESObserverManifestExact as Observer
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoARPESForwardObservationBoundaryExact as Forward

record CoQuarterTaSeTwoMaxCutStatus : Set where
  constructor co-quarter-tase-two-max-cut-status
  field
    bnsMetadataFixed : Bool
    independentOperationEqualityClosed : Bool
    literalBNSConsumedByBlochReceipt : Bool
    blochPhaseImplemented : Bool
    sewingCocycleExecutionClosed : Bool
    spinSpaceGeneratorCrosswalkFixed : Bool
    publishedCrystalBasisFixed : Bool
    publishedDFTRecipeFixed : Bool
    wannierProducerRouteFixed : Bool
    wannierFormatConsumerImplemented : Bool
    materialBasisBNSCovarianceConsumerImplemented : Bool
    wannier3DResponseConsumerImplemented : Bool
    nonAbelianTopologyConsumerImplemented : Bool
    publishedARPESSummaryConstraintsFixed : Bool
    kzCalibrationRouteFixed : Bool
    rawIgorObserverConsumerImplemented : Bool
    independentSOCBandTargetsFixed : Bool
    independentKagomeMechanismFixed : Bool
    sourcedKagomeTBExecutionFixed : Bool
    forwardFitConsumerImplemented : Bool
    materialHamiltonianClosed : Bool
    materialBasisCovarianceClosed : Bool
    co3DSpinTextureClosed : Bool
    coBerryTopologyClosed : Bool
    coSOCContinuationClosed : Bool
    rawARPESPayloadPresent : Bool
    exactSpectralObserverClosed : Bool
    quantitativeFitClosed : Bool
    umbrellaIntegrated : Bool

canonicalCoQuarterTaSeTwoMaxCutStatus : CoQuarterTaSeTwoMaxCutStatus
canonicalCoQuarterTaSeTwoMaxCutStatus =
  co-quarter-tase-two-max-cut-status
    true true true true true true
    true true true true true true true
    true true true
    true true true true
    false false false false false false false false
    true

existingBNSStatus : BNS.OperationSameObjectStatus
existingBNSStatus = BNS.canonicalOperationSameObjectStatus

existingBlochStatus : Bloch.BlochSewingContract
existingBlochStatus = Bloch.canonicalBlochSewingContract

existingMaterialProducerStatus : Material.MaterialHamiltonianProducerStatus
existingMaterialProducerStatus = Material.canonicalMaterialHamiltonianProducerStatus

existingWannierProducerStatus : Wannier.WannierProducerStatus
existingWannierProducerStatus = Wannier.canonicalWannierProducerStatus

existingMaterialBasisCovarianceStatus : WannierBNS.MaterialBasisCovarianceStatus
existingMaterialBasisCovarianceStatus = WannierBNS.canonicalMaterialBasisCovarianceStatus

existingWannier3DResponseStatus : Response3D.Wannier3DResponseStatus
existingWannier3DResponseStatus = Response3D.canonicalWannier3DResponseStatus

existingNonAbelianTopologyStatus : Topology.NonAbelianTopologyStatus
existingNonAbelianTopologyStatus = Topology.canonicalNonAbelianTopologyStatus

existingTopologyAttributionBoundary : Topology.AttributionBoundary
existingTopologyAttributionBoundary = Topology.canonicalAttributionBoundary

existingTransportPromotionBoundary : Topology.TransportPromotionBoundary
existingTransportPromotionBoundary = Topology.canonicalTransportPromotionBoundary

existingPublishedARPESStatus : PublishedARPES.PublishedTargetStatus
existingPublishedARPESStatus = PublishedARPES.canonicalPublishedTargetStatus

existingKzCalibrationBoundary : Kz.KzCrossPollinationBoundary
existingKzCalibrationBoundary = Kz.canonicalKzCrossPollinationBoundary

existingObserverManifestStatus : Observer.ObserverManifestStatus
existingObserverManifestStatus = Observer.canonicalObserverManifestStatus

existingIndependentTheoryBoundary : Independent.CrossValidationPromotionBoundary
existingIndependentTheoryBoundary = Independent.canonicalCrossValidationPromotionBoundary

existingSpinSpaceCrosswalk : SpinSpace.SpinSpaceGeneratorCrosswalk
existingSpinSpaceCrosswalk = SpinSpace.canonicalSpinSpaceGeneratorCrosswalk

existingARPESStatus : ARPES.CoARPESAcquisitionStatus
existingARPESStatus = ARPES.canonicalCoARPESAcquisitionStatus

existingForwardConsumerStatus : Forward.ExecutableConsumerStatus
existingForwardConsumerStatus = Forward.canonicalExecutableConsumerStatus

record IrreduciblePhysicalResidual : Set where
  constructor irreducible-physical-residual
  field
    exactElectronicStructureArtifactNeeded : Bool
    sameBasisMaterialSewingArtifactNeeded : Bool
    sameBasisSpinOperatorArtifactNeeded : Bool
    materialSOCExchangeHamiltonianNeeded : Bool
    rawSpinARPESPayloadNeeded : Bool
    rawARPESCalibrationManifestNeeded : Bool
    calibratedSpectralObserverNeeded : Bool
    co3DResponseExecutionNeeded : Bool
    nonAbelianTopologyExecutionNeeded : Bool
    quantitativeForwardFitNeeded : Bool
    degeneracySafeTransportNeeded : Bool
    furtherAbstractToyLayerNeeded : Bool

canonicalIrreduciblePhysicalResidual : IrreduciblePhysicalResidual
canonicalIrreduciblePhysicalResidual =
  irreducible-physical-residual
    true true true true true true
    true true true true true
    false
