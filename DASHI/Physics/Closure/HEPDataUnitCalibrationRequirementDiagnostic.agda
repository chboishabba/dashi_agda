module DASHI.Physics.Closure.HEPDataUnitCalibrationRequirementDiagnostic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataObservableSchema as HEP

------------------------------------------------------------------------
-- HEP-C: unit/dimension/calibration requirement diagnostic.
--
-- HEP-A names HEPDataUnitSemantics as labels inside the future observable
-- schema.  This module records the stronger HEP-C receipt needed before those
-- labels can support a measured physical calibration claim.  It does not pick
-- physical units, dimensions, scale factors, validation authorities, or any
-- W3/W4/W5 promotion target.

data HEPDataUnitCalibrationValidationAuthorityToken : Set where

validationAuthorityImpossibleHere :
  HEPDataUnitCalibrationValidationAuthorityToken →
  ⊥
validationAuthorityImpossibleHere ()

record HEPDataScaleConventionEvidence : Setω where
  field
    ScaleConventionCarrier :
      Set

    scaleConventionWitness :
      ScaleConventionCarrier

    scaleConventionLabel :
      String

    scaleConventionAuthorityLabel :
      String

record HEPDataDimensionPreservationClaim
  (InternalCarrier MeasuredCarrier PhysicalUnitCarrier DimensionCarrier : Set)
  (dimensionOfUnit : PhysicalUnitCarrier → DimensionCarrier)
  (internalUnit : InternalCarrier → PhysicalUnitCarrier)
  (measuredUnit : MeasuredCarrier → PhysicalUnitCarrier)
  (calibrationMap : InternalCarrier → MeasuredCarrier)
  : Set where
  field
    dimensionPreservation :
      (x : InternalCarrier) →
      dimensionOfUnit (measuredUnit (calibrationMap x))
      ≡
      dimensionOfUnit (internalUnit x)

    preservationBoundaryLabel :
      String

record HEPDataMonotonicityClaim
  (InternalCarrier MeasuredCarrier : Set)
  (calibrationMap : InternalCarrier → MeasuredCarrier)
  : Setω where
  field
    internalOrder :
      InternalCarrier →
      InternalCarrier →
      Set

    measuredOrder :
      MeasuredCarrier →
      MeasuredCarrier →
      Set

    monotonicity :
      (x y : InternalCarrier) →
      internalOrder x y →
      measuredOrder (calibrationMap x) (calibrationMap y)

    monotonicityBoundaryLabel :
      String

data HEPDataPreservationOrMonotonicityClaim
  (InternalCarrier MeasuredCarrier PhysicalUnitCarrier DimensionCarrier : Set)
  (dimensionOfUnit : PhysicalUnitCarrier → DimensionCarrier)
  (internalUnit : InternalCarrier → PhysicalUnitCarrier)
  (measuredUnit : MeasuredCarrier → PhysicalUnitCarrier)
  (calibrationMap : InternalCarrier → MeasuredCarrier)
  : Setω where
  preservationClaim :
    HEPDataDimensionPreservationClaim
      InternalCarrier
      MeasuredCarrier
      PhysicalUnitCarrier
      DimensionCarrier
      dimensionOfUnit
      internalUnit
      measuredUnit
      calibrationMap →
    HEPDataPreservationOrMonotonicityClaim
      InternalCarrier
      MeasuredCarrier
      PhysicalUnitCarrier
      DimensionCarrier
      dimensionOfUnit
      internalUnit
      measuredUnit
      calibrationMap

  monotonicityClaim :
    HEPDataMonotonicityClaim
      InternalCarrier
      MeasuredCarrier
      calibrationMap →
    HEPDataPreservationOrMonotonicityClaim
      InternalCarrier
      MeasuredCarrier
      PhysicalUnitCarrier
      DimensionCarrier
      dimensionOfUnit
      internalUnit
      measuredUnit
      calibrationMap

record HEPDataCalibrationClaimBoundary
  (InternalCarrier MeasuredCarrier PhysicalUnitCarrier DimensionCarrier : Set)
  (dimensionOfUnit : PhysicalUnitCarrier → DimensionCarrier)
  (internalUnit : InternalCarrier → PhysicalUnitCarrier)
  (measuredUnit : MeasuredCarrier → PhysicalUnitCarrier)
  (calibrationMap : InternalCarrier → MeasuredCarrier)
  : Setω where
  field
    preservationOrMonotonicity :
      HEPDataPreservationOrMonotonicityClaim
        InternalCarrier
        MeasuredCarrier
        PhysicalUnitCarrier
        DimensionCarrier
        dimensionOfUnit
        internalUnit
        measuredUnit
        calibrationMap

    claimBoundaryLabel :
      String

record HEPDataUnitCalibrationRequirementReceipt
  (observable : HEP.HEPDataObservable)
  : Setω where
  field
    schemaSurface :
      HEP.HEPDataObservableSchemaSurface

    schemaSurfaceMatchesObservable :
      schemaSurface ≡ HEP.HEPDataObservable.schema observable

    unitSemantics :
      HEP.HEPDataUnitSemantics

    unitSemanticsMatchesSchema :
      unitSemantics
      ≡
      HEP.HEPDataObservableSchemaSurface.unitSemantics schemaSurface

    PhysicalUnitCarrier :
      Set

    DimensionCarrier :
      Set

    dimensionOfUnit :
      PhysicalUnitCarrier →
      DimensionCarrier

    observablePhysicalUnit :
      PhysicalUnitCarrier

    observableDimension :
      DimensionCarrier

    observableDimensionMatchesUnit :
      dimensionOfUnit observablePhysicalUnit ≡ observableDimension

    InternalCarrier :
      Set

    MeasuredCarrier :
      Set

    internalUnit :
      InternalCarrier →
      PhysicalUnitCarrier

    measuredUnit :
      MeasuredCarrier →
      PhysicalUnitCarrier

    conversionCalibrationMap :
      InternalCarrier →
      MeasuredCarrier

    scaleConventionEvidence :
      HEPDataScaleConventionEvidence

    scaleConventionMatchesSchema :
      HEPDataScaleConventionEvidence.scaleConventionLabel
        scaleConventionEvidence
      ≡
      HEP.HEPDataUnitSemantics.scaleConvention unitSemantics

    preservationOrMonotonicityBoundary :
      HEPDataCalibrationClaimBoundary
        InternalCarrier
        MeasuredCarrier
        PhysicalUnitCarrier
        DimensionCarrier
        dimensionOfUnit
        internalUnit
        measuredUnit
        conversionCalibrationMap

    validationAuthority :
      HEPDataUnitCalibrationValidationAuthorityToken

    validationAuthorityLabel :
      String

    consumerWiringTarget :
      String

unitCalibrationRequirementReceiptImpossibleHere :
  {observable : HEP.HEPDataObservable} →
  HEPDataUnitCalibrationRequirementReceipt observable →
  ⊥
unitCalibrationRequirementReceiptImpossibleHere receipt =
  validationAuthorityImpossibleHere
    (HEPDataUnitCalibrationRequirementReceipt.validationAuthority receipt)

data HEPDataUnitCalibrationSourceAvailability : Set where
  schemaLabelOnly :
    HEPDataUnitCalibrationSourceAvailability
  missingFromCurrentRepo :
    HEPDataUnitCalibrationSourceAvailability

record HEPDataUnitCalibrationAvailability : Set where
  field
    observableSchemaSurface :
      HEPDataUnitCalibrationSourceAvailability

    unitSemanticsLabels :
      HEPDataUnitCalibrationSourceAvailability

    physicalUnitCarrier :
      HEPDataUnitCalibrationSourceAvailability

    dimensionCarrier :
      HEPDataUnitCalibrationSourceAvailability

    dimensionOfUnitMap :
      HEPDataUnitCalibrationSourceAvailability

    conversionCalibrationMap :
      HEPDataUnitCalibrationSourceAvailability

    scaleConventionEvidence :
      HEPDataUnitCalibrationSourceAvailability

    preservationOrMonotonicityLaw :
      HEPDataUnitCalibrationSourceAvailability

    validationAuthority :
      HEPDataUnitCalibrationSourceAvailability

canonicalHEPDataUnitCalibrationAvailability :
  HEPDataUnitCalibrationAvailability
canonicalHEPDataUnitCalibrationAvailability =
  record
    { observableSchemaSurface =
        schemaLabelOnly
    ; unitSemanticsLabels =
        schemaLabelOnly
    ; physicalUnitCarrier =
        missingFromCurrentRepo
    ; dimensionCarrier =
        missingFromCurrentRepo
    ; dimensionOfUnitMap =
        missingFromCurrentRepo
    ; conversionCalibrationMap =
        missingFromCurrentRepo
    ; scaleConventionEvidence =
        missingFromCurrentRepo
    ; preservationOrMonotonicityLaw =
        missingFromCurrentRepo
    ; validationAuthority =
        missingFromCurrentRepo
    }

data HEPDataUnitCalibrationMissingRequirement : Set where
  missingSelectedHEPDataObservable :
    HEPDataUnitCalibrationMissingRequirement
  missingPhysicalUnitCarrier :
    HEPDataUnitCalibrationMissingRequirement
  missingDimensionCarrier :
    HEPDataUnitCalibrationMissingRequirement
  missingDimensionOfUnitMap :
    HEPDataUnitCalibrationMissingRequirement
  missingObservablePhysicalUnit :
    HEPDataUnitCalibrationMissingRequirement
  missingInternalAndMeasuredCarriers :
    HEPDataUnitCalibrationMissingRequirement
  missingConversionCalibrationMap :
    HEPDataUnitCalibrationMissingRequirement
  missingScaleConventionEvidence :
    HEPDataUnitCalibrationMissingRequirement
  missingPreservationOrMonotonicityClaimBoundary :
    HEPDataUnitCalibrationMissingRequirement
  missingValidationAuthority :
    HEPDataUnitCalibrationMissingRequirement
  missingUnitCalibrationRequirementReceipt :
    HEPDataUnitCalibrationMissingRequirement

canonicalHEPDataUnitCalibrationMissingRequirements :
  List HEPDataUnitCalibrationMissingRequirement
canonicalHEPDataUnitCalibrationMissingRequirements =
  missingSelectedHEPDataObservable
  ∷ missingPhysicalUnitCarrier
  ∷ missingDimensionCarrier
  ∷ missingDimensionOfUnitMap
  ∷ missingObservablePhysicalUnit
  ∷ missingInternalAndMeasuredCarriers
  ∷ missingConversionCalibrationMap
  ∷ missingScaleConventionEvidence
  ∷ missingPreservationOrMonotonicityClaimBoundary
  ∷ missingValidationAuthority
  ∷ missingUnitCalibrationRequirementReceipt
  ∷ []

data HEPDataUnitCalibrationCurrentStatus : Set where
  blockedAwaitingSelectedObservableAndExternalCalibration :
    HEPDataUnitCalibrationCurrentStatus

record HEPDataUnitCalibrationRequirementDiagnostic : Setω where
  field
    schemaRequestDiagnostic :
      HEP.HEPDataObservableSchemaRequestDiagnostic

    schemaStatus :
      HEP.HEPDataObservableSchemaCurrentStatus

    schemaStatusStillUnpromoted :
      schemaStatus ≡ HEP.schemaSurfaceDefinedButObservableUnpromoted

    currentStatus :
      HEPDataUnitCalibrationCurrentStatus

    sourceAvailability :
      HEPDataUnitCalibrationAvailability

    sourceAvailabilityIsCanonical :
      sourceAvailability ≡ canonicalHEPDataUnitCalibrationAvailability

    missingRequirements :
      List HEPDataUnitCalibrationMissingRequirement

    missingRequirementsAreCanonical :
      missingRequirements
      ≡
      canonicalHEPDataUnitCalibrationMissingRequirements

    futureReceiptName :
      String

    exactRequiredReceiptFields :
      List String

    currentSchemaLabelFields :
      List String

    noFabricationBoundary :
      List String

    blockerImpact :
      List String

    impossibleValidationAuthorityHere :
      HEPDataUnitCalibrationValidationAuthorityToken →
      ⊥

    impossibleReceiptHere :
      {observable : HEP.HEPDataObservable} →
      HEPDataUnitCalibrationRequirementReceipt observable →
      ⊥

canonicalHEPDataUnitCalibrationRequirementDiagnostic :
  HEPDataUnitCalibrationRequirementDiagnostic
canonicalHEPDataUnitCalibrationRequirementDiagnostic =
  record
    { schemaRequestDiagnostic =
        HEP.canonicalHEPDataObservableSchemaRequestDiagnostic
    ; schemaStatus =
        HEP.canonicalHEPDataObservableSchemaCurrentStatus
    ; schemaStatusStillUnpromoted =
        refl
    ; currentStatus =
        blockedAwaitingSelectedObservableAndExternalCalibration
    ; sourceAvailability =
        canonicalHEPDataUnitCalibrationAvailability
    ; sourceAvailabilityIsCanonical =
        refl
    ; missingRequirements =
        canonicalHEPDataUnitCalibrationMissingRequirements
    ; missingRequirementsAreCanonical =
        refl
    ; futureReceiptName =
        "DASHI.Physics.Closure.HEPDataUnitCalibrationRequirementDiagnostic.HEPDataUnitCalibrationRequirementReceipt"
    ; exactRequiredReceiptFields =
        "observable : HEPDataObservable parameter selected by HEP-B"
        ∷ "schemaSurface and proof it is HEPDataObservable.schema observable"
        ∷ "unitSemantics and proof it is schemaSurface.unitSemantics"
        ∷ "PhysicalUnitCarrier : Set"
        ∷ "DimensionCarrier : Set"
        ∷ "dimensionOfUnit : PhysicalUnitCarrier -> DimensionCarrier"
        ∷ "observablePhysicalUnit : PhysicalUnitCarrier"
        ∷ "observableDimension : DimensionCarrier"
        ∷ "observableDimensionMatchesUnit proof"
        ∷ "InternalCarrier : Set and MeasuredCarrier : Set"
        ∷ "internalUnit and measuredUnit assignments"
        ∷ "conversionCalibrationMap : InternalCarrier -> MeasuredCarrier"
        ∷ "scaleConventionEvidence matching HEPDataUnitSemantics.scaleConvention"
        ∷ "preservationOrMonotonicityBoundary with either dimension preservation or monotonicity"
        ∷ "validationAuthority : HEPDataUnitCalibrationValidationAuthorityToken"
        ∷ "validationAuthorityLabel and consumerWiringTarget"
        ∷ []
    ; currentSchemaLabelFields =
        "HEPDataUnitSemantics.observableQuantity : String"
        ∷ "HEPDataUnitSemantics.unitLabel : String"
        ∷ "HEPDataUnitSemantics.dimensionLabel : String"
        ∷ "HEPDataUnitSemantics.scaleConvention : String"
        ∷ "HEPDataUnitSemantics.conversionToInternalCarrier : String"
        ∷ []
    ; noFabricationBoundary =
        "HEPDataObservableSchema supplies unit/dimension/scale/conversion labels only"
        ∷ "This HEP-C diagnostic does not choose SI units or any other physical unit carrier"
        ∷ "This HEP-C diagnostic does not choose a dimension carrier or dimensionOfUnit map"
        ∷ "This HEP-C diagnostic does not construct conversionCalibrationMap, scale evidence, preservation, or monotonicity"
        ∷ "HEPDataUnitCalibrationValidationAuthorityToken has no constructor in this module"
        ∷ "No W3 empirical authority, W4 physical calibration, or W5 GR/QFT promotion is constructed here"
        ∷ []
    ; blockerImpact =
        "HEP-C remains blocked until HEP-B selects a concrete HEPDataObservable and an external calibration provider supplies the receipt fields"
        ∷ "The existing schema labels are useful requirements, but they are not physical-unit authority"
        ∷ "Downstream projection/comparison lanes must not treat unit labels as calibrated measured quantities"
        ∷ []
    ; impossibleValidationAuthorityHere =
        validationAuthorityImpossibleHere
    ; impossibleReceiptHere =
        unitCalibrationRequirementReceiptImpossibleHere
    }
