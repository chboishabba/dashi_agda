module DASHI.Biology.Levin.MitochondrialPerturbationObservability where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Falsifiable perturbation surface for the mitochondrial oscillator model.
-- Inputs and predicted observables are kept distinct from interpretation.

data PerturbationKind : Set where
  oxygenStep : PerturbationKind
  pyruvateStep : PerturbationKind
  pHStep : PerturbationKind
  temperatureStep : PerturbationKind
  membranePotentialStep : PerturbationKind
  ADPATPShift : PerturbationKind
  reverseElectronTransportGate : PerturbationKind

data ObservableKind : Set where
  rotorFrequency : ObservableKind
  cristaShapeMode : ObservableKind
  junctionFlux : ObservableKind
  membranePotential : ObservableKind
  protonMotiveForce : ObservableKind
  ATPProductionRate : ObservableKind
  interCristaPhaseRelation : ObservableKind

record PerturbationReceipt : Set where
  field
    perturbation : PerturbationKind
    observable : ObservableKind
    baselineMeasured : Bool
    responseMeasured : Bool
    repeatable : Bool
    modelDiscriminating : Bool

record MitochondrialPerturbationBoundary : Set where
  field
    canonicalPerturbations : List PerturbationKind
    canonicalObservables : List ObservableKind

    imagingAloneIsNotMechanism : Bool
    imagingAloneIsNotMechanismIsFalse : imagingAloneIsNotMechanism ≡ false

    correlationAloneIsNotPLL : Bool
    correlationAloneIsNotPLLIsFalse : correlationAloneIsNotPLL ≡ false

    syntheticConstructWouldStrengthenClaim : Bool
    syntheticConstructWouldStrengthenClaimIsTrue : syntheticConstructWouldStrengthenClaim ≡ true

    reading : String

open MitochondrialPerturbationBoundary public

canonicalMitochondrialPerturbationBoundary : MitochondrialPerturbationBoundary
canonicalMitochondrialPerturbationBoundary = record
  { canonicalPerturbations = oxygenStep ∷ pyruvateStep ∷ pHStep ∷ temperatureStep ∷ membranePotentialStep ∷ ADPATPShift ∷ reverseElectronTransportGate ∷ []
  ; canonicalObservables = rotorFrequency ∷ cristaShapeMode ∷ junctionFlux ∷ membranePotential ∷ protonMotiveForce ∷ ATPProductionRate ∷ interCristaPhaseRelation ∷ []
  ; imagingAloneIsNotMechanism = false
  ; imagingAloneIsNotMechanismIsFalse = refl
  ; correlationAloneIsNotPLL = false
  ; correlationAloneIsNotPLLIsFalse = refl
  ; syntheticConstructWouldStrengthenClaim = true
  ; syntheticConstructWouldStrengthenClaimIsTrue = refl
  ; reading = "A useful mitochondrial oscillator theory must predict perturbation-specific phase, flux, shape, or production responses that distinguish it from ordinary biochemical feedback models"
  }
