module DASHI.Biology.AvianMagnetoreceptionEMExposureTransportExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AvianMagneticFieldPerturbationReceipt as Perturb
import DASHI.Biology.MagnetoreceptionSurface as Generic
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as EM

------------------------------------------------------------------------
-- EXPERIMENTAL EM EXPOSURE TRANSPORT
--
-- Keep five experimentally distinct objects separate:
--
--   commanded apparatus state
--      -> generated electromagnetic field
--      -> measured chamber field
--      -> animal-position exposure
--      -> receptor-tissue exposure
--
-- The final two transports require geometry/material/calibration receipts.
-- A commanded current/phase/frequency value is not itself the biological
-- exposure, and a chamber measurement is not automatically the field at the
-- microscopic receptor.
------------------------------------------------------------------------

data ExposureStage : Set where
  commandedApparatusState : ExposureStage
  generatedFieldState : ExposureStage
  measuredChamberFieldState : ExposureStage
  animalPositionExposureState : ExposureStage
  receptorTissueExposureState : ExposureStage
  biologicalResponseState : ExposureStage

data ExposureTransportStatus : Set where
  commandedOnly : ExposureTransportStatus
  synthesisModelRequired : ExposureTransportStatus
  calibrationReceiptRequired : ExposureTransportStatus
  spatialTransportRequired : ExposureTransportStatus
  tissueTransportRequired : ExposureTransportStatus
  biologicalCouplingRequired : ExposureTransportStatus

data ExposureBoundary : Set where
  noCommandEqualsGeneratedFieldClaim : ExposureBoundary
  noGeneratedEqualsMeasuredFieldClaim : ExposureBoundary
  noChamberMeasurementEqualsAnimalExposureClaim : ExposureBoundary
  noAnimalExposureEqualsReceptorExposureClaim : ExposureBoundary
  noReceptorExposureIdentifiesMechanismClaim : ExposureBoundary
  noExposureToBehaviorClosureClaim : ExposureBoundary
  noSIUnitsProveMaxwellLawClaim : ExposureBoundary

statusAt : ExposureStage -> ExposureTransportStatus
statusAt commandedApparatusState = commandedOnly
statusAt generatedFieldState = synthesisModelRequired
statusAt measuredChamberFieldState = calibrationReceiptRequired
statusAt animalPositionExposureState = spatialTransportRequired
statusAt receptorTissueExposureState = tissueTransportRequired
statusAt biologicalResponseState = biologicalCouplingRequired

canonicalExposureStages : List ExposureStage
canonicalExposureStages =
  commandedApparatusState
  ∷ generatedFieldState
  ∷ measuredChamberFieldState
  ∷ animalPositionExposureState
  ∷ receptorTissueExposureState
  ∷ biologicalResponseState
  ∷ []

canonicalExposureBoundaries : List ExposureBoundary
canonicalExposureBoundaries =
  noCommandEqualsGeneratedFieldClaim
  ∷ noGeneratedEqualsMeasuredFieldClaim
  ∷ noChamberMeasurementEqualsAnimalExposureClaim
  ∷ noAnimalExposureEqualsReceptorExposureClaim
  ∷ noReceptorExposureIdentifiesMechanismClaim
  ∷ noExposureToBehaviorClosureClaim
  ∷ noSIUnitsProveMaxwellLawClaim
  ∷ []

record EMExposureTransportSurface : Set₁ where
  field
    CommandState : Set
    GeneratedField : Set
    MeasuredField : Set
    AnimalExposure : Set
    ReceptorExposure : Set
    BiologicalResponse : Set

    synthesizeCandidate :
      CommandState -> GeneratedField

    measureCandidate :
      GeneratedField -> MeasuredField

    transportToAnimalCandidate :
      MeasuredField -> AnimalExposure

    transportToReceptorCandidate :
      AnimalExposure -> ReceptorExposure

    biologicalResponseCandidate :
      ReceptorExposure -> BiologicalResponse

    synthesisValidated :
      Bool

    calibrationValidated :
      Bool

    animalPositionTransportValidated :
      Bool

    receptorTissueTransportValidated :
      Bool

    receptorMechanismIdentified :
      Bool

    stages :
      List ExposureStage

    boundaries :
      List ExposureBoundary

    reading :
      String

open EMExposureTransportSurface public

data ExposureToken : Set where
  commandToken : ExposureToken
  generatedToken : ExposureToken
  measuredToken : ExposureToken
  animalExposureToken : ExposureToken
  receptorExposureToken : ExposureToken
  responseToken : ExposureToken

canonicalEMExposureTransportSurface : EMExposureTransportSurface
canonicalEMExposureTransportSurface =
  record
    { CommandState = ExposureToken
    ; GeneratedField = ExposureToken
    ; MeasuredField = ExposureToken
    ; AnimalExposure = ExposureToken
    ; ReceptorExposure = ExposureToken
    ; BiologicalResponse = ExposureToken
    ; synthesizeCandidate = λ _ -> generatedToken
    ; measureCandidate = λ _ -> measuredToken
    ; transportToAnimalCandidate = λ _ -> animalExposureToken
    ; transportToReceptorCandidate = λ _ -> receptorExposureToken
    ; biologicalResponseCandidate = λ _ -> responseToken
    ; synthesisValidated = false
    ; calibrationValidated = false
    ; animalPositionTransportValidated = false
    ; receptorTissueTransportValidated = false
    ; receptorMechanismIdentified = false
    ; stages = canonicalExposureStages
    ; boundaries = canonicalExposureBoundaries
    ; reading =
        "Command, generated field, measured chamber field, animal-position exposure, receptor-tissue exposure, and biological response remain separately typed until producer-specific validation receipts are supplied."
    }

record AvianMagnetoreceptionEMExposureTransportReceipt : Set₁ where
  field
    exposureSurface :
      EMExposureTransportSurface

    exposureSurfaceIsCanonical :
      exposureSurface ≡ canonicalEMExposureTransportSurface

    perturbationReceipt :
      Perturb.AvianMagneticFieldPerturbationReceipt
        Generic.canonicalMechanismNeutralMagnetoreceptionSurface

    u1Boundary :
      EM.U1ElectromagneticBoundary

    u1BoundaryIsCanonical :
      u1Boundary ≡ EM.canonicalU1ElectromagneticBoundary

    generatedFieldIsValidated :
      Bool

    generatedFieldIsValidatedIsFalse :
      generatedFieldIsValidated ≡ false

    measuredFieldIsReceptorExposure :
      Bool

    measuredFieldIsReceptorExposureIsFalse :
      measuredFieldIsReceptorExposure ≡ false

    fieldAtReceptorRecovered :
      Bool

    fieldAtReceptorRecoveredIsFalse :
      fieldAtReceptorRecovered ≡ false

    receptorMechanismRecovered :
      Bool

    receptorMechanismRecoveredIsFalse :
      receptorMechanismRecovered ≡ false

    receiptReading :
      String

open AvianMagnetoreceptionEMExposureTransportReceipt public


canonicalAvianMagnetoreceptionEMExposureTransportReceipt :
  AvianMagnetoreceptionEMExposureTransportReceipt
canonicalAvianMagnetoreceptionEMExposureTransportReceipt =
  record
    { exposureSurface = canonicalEMExposureTransportSurface
    ; exposureSurfaceIsCanonical = refl
    ; perturbationReceipt =
        Perturb.canonicalMechanismNeutralPerturbationReceipt
    ; u1Boundary = EM.canonicalU1ElectromagneticBoundary
    ; u1BoundaryIsCanonical = refl
    ; generatedFieldIsValidated = false
    ; generatedFieldIsValidatedIsFalse = refl
    ; measuredFieldIsReceptorExposure = false
    ; measuredFieldIsReceptorExposureIsFalse = refl
    ; fieldAtReceptorRecovered = false
    ; fieldAtReceptorRecoveredIsFalse = refl
    ; receptorMechanismRecovered = false
    ; receptorMechanismRecoveredIsFalse = refl
    ; receiptReading =
        "The EM application socket and perturbation receipt are present, but synthesis, calibration, spatial transport, tissue exposure, and receptor identification remain independent validation obligations."
    }
