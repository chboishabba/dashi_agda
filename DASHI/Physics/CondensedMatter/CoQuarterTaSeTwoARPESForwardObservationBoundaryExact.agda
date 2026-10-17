module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoARPESForwardObservationBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.CondensedMatter.ARPESBandFoldingWitnessGateExact as GenericARPES
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoPublishedARPESConstraintsExact as Published
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoIndependentTheoryCrossValidationExact as Independent

------------------------------------------------------------------------
-- MATERIAL SPECTRUM -> INSTRUMENT -> CALIBRATED ARPES OBSERVER
--
-- Productive cross-pollination: DASHI imaging lanes already enforce the useful
-- architecture latent field -> calibrated response operator -> detector
-- observation -> inverse/fit, rather than identifying the latent field with
-- the recorded array.  Here we instantiate that architecture for ARPES only at
-- the obligation level and pair it with the executable consumer
-- scripts/co_tase2_arpes_forward_fit.py.
--
-- This module does not manufacture matrix elements, kz broadening, detector
-- efficiency, a material Hamiltonian, or raw ARPES.  Those must be supplied by
-- same-object artifacts before the consumer can issue a quantitative receipt.
------------------------------------------------------------------------

record ARPESForwardObservationContract : Set where
  constructor arpes-forward-observation-contract
  field
    materialSpectralFunctionArtifactRequired : Bool
    spectralArtifactMustIncludeSOC : Bool
    spectralArtifactMustIncludeExchange : Bool
    fermiOccupationApplied : Bool
    energyResolutionKernelApplied : Bool
    momentumResolutionKernelApplied : Bool
    matrixElementModelMustBeDeclared : Bool
    kzBroadeningModelMustBeDeclared : Bool
    backgroundModelMustBeDeclared : Bool
    spinPolarimeterCalibrationMustBeDeclared : Bool
    rawObserverUncertaintyRequired : Bool
    heldOutResidualRequired : Bool

open ARPESForwardObservationContract public

canonicalARPESForwardObservationContract : ARPESForwardObservationContract
canonicalARPESForwardObservationContract =
  arpes-forward-observation-contract
    true true true true true true
    true true true true true true

record ExecutableConsumerStatus : Set where
  constructor executable-consumer-status
  field
    strictMaterialNPZSchemaImplemented : Bool
    strictCalibratedARPESNPZSchemaImplemented : Bool
    provenanceSHA256Required : Bool
    socAndExchangeFailClosed : Bool
    spinCalibrationFailClosed : Bool
    deterministicInterpolationImplemented : Bool
    fermiFactorImplemented : Bool
    gaussianResolutionImplemented : Bool
    nuisanceScaleAndBackgroundOnly : Bool
    reproducibleTrainHoldoutSplit : Bool
    literalMaterialArtifactPresent : Bool
    literalRawARPESArtifactPresent : Bool
    quantitativeReceiptExecuted : Bool

canonicalExecutableConsumerStatus : ExecutableConsumerStatus
canonicalExecutableConsumerStatus =
  executable-consumer-status
    true true true true true true true true true true
    false false false

-- The generic spectral observer remains the target type.  Its existence is not
-- inferred from the publication summaries or from the independent theory paper.
existingGenericWitnessBoundary : GenericARPES.WitnessPromotionBoundary
existingGenericWitnessBoundary = GenericARPES.canonicalWitnessPromotionBoundary

existingPublishedTargetStatus : Published.PublishedTargetStatus
existingPublishedTargetStatus = Published.canonicalPublishedTargetStatus

existingIndependentTheoryBoundary : Independent.CrossValidationPromotionBoundary
existingIndependentTheoryBoundary = Independent.canonicalCrossValidationPromotionBoundary

record ForwardFitPromotionBoundary : Set where
  constructor forward-fit-promotion-boundary
  field
    executableConsumerImpliesMaterialArtifact : Bool
    executableConsumerImpliesRawObserver : Bool
    publicationResolutionImpliesFullInstrumentModel : Bool
    nuisanceFitMayHideMissingMatrixElementPhysics : Bool
    missingKzModelMayBeSilentlyIgnored : Bool
    successfulFutureReceiptRequiresBothLiteralArtifacts : Bool

canonicalForwardFitPromotionBoundary : ForwardFitPromotionBoundary
canonicalForwardFitPromotionBoundary =
  forward-fit-promotion-boundary
    false false false false false true
