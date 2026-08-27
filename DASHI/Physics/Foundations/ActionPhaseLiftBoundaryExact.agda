module DASHI.Physics.Foundations.ActionPhaseLiftBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Generic boundary between an accumulated action carrier and a phase carrier.
--
-- Having an action-like scalar is not enough to obtain quantum phase.  A
-- phase lift requires an explicit calibration/periodicity rule (physically,
-- this is where the S/hbar structure would have to enter).
------------------------------------------------------------------------

record ActionPhaseLift : Set₁ where
  field
    ActionCarrier : Set
    PhaseCarrier : Set
    CalibrationCarrier : Set

    phaseLift : CalibrationCarrier → ActionCarrier → PhaseCarrier
    phaseReading : String

open ActionPhaseLift public

record ActionPhaseCalibrationWitness (surface : ActionPhaseLift) : Set where
  field
    calibration : CalibrationCarrier surface
    calibrationReading : String

open ActionPhaseCalibrationWitness public

record ActionPhaseLiftBoundary : Set where
  constructor actionPhaseLiftBoundary
  field
    actionValueIsAlreadyPhase : Bool
    actionValueIsAlreadyPhaseIsFalse :
      actionValueIsAlreadyPhase ≡ false

    additiveActionDeterminesHbarCalibration : Bool
    additiveActionDeterminesHbarCalibrationIsFalse :
      additiveActionDeterminesHbarCalibration ≡ false

    phaseLabelIsAlreadyProbability : Bool
    phaseLabelIsAlreadyProbabilityIsFalse :
      phaseLabelIsAlreadyProbability ≡ false

    structuralActionCandidateDeterminesFeynmanAmplitude : Bool
    structuralActionCandidateDeterminesFeynmanAmplitudeIsFalse :
      structuralActionCandidateDeterminesFeynmanAmplitude ≡ false

canonicalActionPhaseLiftBoundary : ActionPhaseLiftBoundary
canonicalActionPhaseLiftBoundary =
  actionPhaseLiftBoundary
    false refl
    false refl
    false refl
    false refl
