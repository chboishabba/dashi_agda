module DASHI.Physics.Foundations.TSFVFeynmanDerivationObligationsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Exact map of the remaining hard arrows.
------------------------------------------------------------------------

data ObligationStatus : Set where
  interfaceOnly : ObligationStatus
  structuralCandidateOnly : ObligationStatus
  finiteShadowOnly : ObligationStatus
  sourceBackedBoundaryOnly : ObligationStatus
  kernelReceiptMissing : ObligationStatus
  derived : ObligationStatus

data DerivationArrow : Set where
  kernelTypecheckReceipt : DerivationArrow
  analyticProjectionCriticality : DerivationArrow
  quantitativeStationaryPhase : DerivationArrow
  realPhysicalScaleCalibration : DerivationArrow
  tsfvToPhysicalAdmissibility : DerivationArrow
  tsfvToNonseparableTransitionAction : DerivationArrow
  tsfvToPhysicalAction : DerivationArrow
  actionToPhaseOverHbar : DerivationArrow
  phaseToFeynmanAmplitudeMeasure : DerivationArrow
  finiteToContinuumPropagator : DerivationArrow
  tsfvSpecificEmpiricalDiscriminator : DerivationArrow

record DerivationObligation : Set where
  constructor derivationObligation
  field
    arrow : DerivationArrow
    status : ObligationStatus
    obligationReading : String

open DerivationObligation public

kernelReceiptObligation : DerivationObligation
kernelReceiptObligation = derivationObligation
  kernelTypecheckReceipt
  kernelReceiptMissing
  "Focused Agda kernel/typecheck receipt is required before the PR tranche is promoted as compiling."

projectionCriticalityObligation : DerivationObligation
projectionCriticalityObligation = derivationObligation
  analyticProjectionCriticality
  finiteShadowOnly
  "Current caustic machinery proves finite many-to-one projection witnesses; an analytic derivative/rank-deficiency theorem such as det(D pi)=0 remains to be constructed."

stationaryPhaseObligation : DerivationObligation
stationaryPhaseObligation = derivationObligation
  quantitativeStationaryPhase
  interfaceOnly
  "Current stationarity taxonomy separates minima, saddles and shortest paths; a controlled asymptotic stationary-phase theorem remains open."

physicalScaleObligation : DerivationObligation
physicalScaleObligation = derivationObligation
  realPhysicalScaleCalibration
  finiteShadowOnly
  "Exact Nat/rational-coordinate source-scale identities exist; real-valued unit calibration including constants such as 2*pi remains downstream."

tsfvAdmissibilityObligation : DerivationObligation
tsfvAdmissibilityObligation = derivationObligation
  tsfvToPhysicalAdmissibility
  interfaceOnly
  "A TSFV-originating theorem must explain why the physically relevant histories are admissible rather than merely accepting a supplied admissibility fibre."

tsfvNonseparableTransitionActionObligation : DerivationObligation
tsfvNonseparableTransitionActionObligation = derivationObligation
  tsfvToNonseparableTransitionAction
  derived
  "A structural Candidate256 transition kernel is now derived from the existing quotient U-coordinate mismatch geometry. It is genuinely nonseparable on the canonical left/right witness and exactly invariant under simultaneous Candidate256 T on both endpoints. This closes only the structural nonseparable-kernel arrow; it is not yet a calibrated physical action."

tsfvActionObligation : DerivationObligation
tsfvActionObligation = derivationObligation
  tsfvToPhysicalAction
  structuralCandidateOnly
  "Additive finite-history action machinery now consumes a derived T-invariant nonseparable TSFV transition kernel, but physical action units, a dynamical/Lagrangian origin, continuum control and empirical calibration remain open."

actionPhaseObligation : DerivationObligation
actionPhaseObligation = derivationObligation
  actionToPhaseOverHbar
  interfaceOnly
  "An explicit action-to-phase lift interface now records the missing calibration carrier; standard theory and experiment support S/hbar, but TSFV supplies neither a physical action calibration nor the hbar/periodicity lift."

amplitudeMeasureObligation : DerivationObligation
amplitudeMeasureObligation = derivationObligation
  phaseToFeynmanAmplitudeMeasure
  sourceBackedBoundaryOnly
  "The Feynman amplitude form is source-backed and experimentally supported in the tested finite reconstruction, but has not been generated from TSFV structure."

continuumPropagatorObligation : DerivationObligation
continuumPropagatorObligation = derivationObligation
  finiteToContinuumPropagator
  interfaceOnly
  "A controlled continuum/appropriate-limit theorem from finite TSFV/path-fibre structure to the known propagator remains open."

empiricalDiscriminatorObligation : DerivationObligation
empiricalDiscriminatorObligation = derivationObligation
  tsfvSpecificEmpiricalDiscriminator
  interfaceOnly
  "Even a successful reproduction of ordinary quantum mechanics requires a TSFV-specific empirical discriminator in admissibility, boundary dependence, phase corrections, caustics, scaling or another observable."

canonicalRemainingObligations : List DerivationObligation
canonicalRemainingObligations =
  kernelReceiptObligation
  ∷ projectionCriticalityObligation
  ∷ stationaryPhaseObligation
  ∷ physicalScaleObligation
  ∷ tsfvAdmissibilityObligation
  ∷ tsfvNonseparableTransitionActionObligation
  ∷ tsfvActionObligation
  ∷ actionPhaseObligation
  ∷ amplitudeMeasureObligation
  ∷ continuumPropagatorObligation
  ∷ empiricalDiscriminatorObligation
  ∷ []

record TSFVFeynmanDerivationBoundary : Set where
  constructor tsfvFeynmanDerivationBoundary
  field
    architectureCompatibleWithFeynman : Bool
    architectureCompatibleWithFeynmanIsTrue :
      architectureCompatibleWithFeynman ≡ true

    structuralActionCandidateConstructed : Bool
    structuralActionCandidateConstructedIsTrue :
      structuralActionCandidateConstructed ≡ true

    nonseparableTransitionActionDerived : Bool
    nonseparableTransitionActionDerivedIsTrue :
      nonseparableTransitionActionDerived ≡ true

    actionToPhaseCalibrationSupplied : Bool
    actionToPhaseCalibrationSuppliedIsFalse :
      actionToPhaseCalibrationSupplied ≡ false

    tsfvCurrentlyDerivesFeynmanPropagator : Bool
    tsfvCurrentlyDerivesFeynmanPropagatorIsFalse :
      tsfvCurrentlyDerivesFeynmanPropagator ≡ false

    tsfvCurrentlyHasUniqueEmpiricalPrediction : Bool
    tsfvCurrentlyHasUniqueEmpiricalPredictionIsFalse :
      tsfvCurrentlyHasUniqueEmpiricalPrediction ≡ false

canonicalTSFVFeynmanDerivationBoundary : TSFVFeynmanDerivationBoundary
canonicalTSFVFeynmanDerivationBoundary =
  tsfvFeynmanDerivationBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
