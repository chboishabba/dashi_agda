module DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalHyperfabricExact as H

------------------------------------------------------------------------
-- Candidate mechanism families.
------------------------------------------------------------------------

data MechanismFamily : Set where
  liTorrCoherentGravity : MechanismFamily
  podkletnovWeightAnomaly : MechanismFamily
  impulsiveSuperconductor : MechanismFamily
  electrohydrodynamicForce : MechanismFamily
  woodwardInertialVariation : MechanismFamily
  negativeMassConstitutive : MechanismFamily
  metricEngineering : MechanismFamily
  ordinaryMechanicalOrEM : MechanismFamily

------------------------------------------------------------------------
-- Observables stay typed.  No "antigravity observed" scalar is admitted.
------------------------------------------------------------------------

data Observable : Set where
  staticWeightChange : Observable
  freeFallAccelerationChange : Observable
  localTestMassAcceleration : Observable
  apparatusImpulse : Observable
  vacuumPersistentThrust : Observable
  interferometricPhaseShift : Observable
  orientationDependentEffect : Observable
  inertialResponseChange : Observable
  metricOrClockShift : Observable

record ObservationReceipt : Set where
  constructor observation-receipt
  field
    observable : Observable
    ordinaryEMClosed ordinaryMechanicalClosed thermalClosed expelledMatterClosed : Bool
    replicated : Bool
    note : String

open ObservationReceipt public

------------------------------------------------------------------------
-- Forward mechanism signatures.
------------------------------------------------------------------------

record MechanismSignature : Set where
  constructor mechanism-signature
  field
    family : MechanismFamily
    requiresCoherentPhase : Bool
    requiresStrongEM : Bool
    requiresRotation : Bool
    modifiesInertialCoordinate : Bool
    modifiesGravityFieldCoordinate : Bool
    modifiesMomentumCoordinate : Bool
    knownOrdinaryMomentumRouteExists : Bool

open MechanismSignature public

liTorrSignature : MechanismSignature
liTorrSignature =
  mechanism-signature liTorrCoherentGravity true true false false true false false

podkletnovSignature : MechanismSignature
podkletnovSignature =
  mechanism-signature podkletnovWeightAnomaly true true true false true false false

impulsiveSuperconductorSignature : MechanismSignature
impulsiveSuperconductorSignature =
  mechanism-signature impulsiveSuperconductor true true false false false true false

electrohydrodynamicSignature : MechanismSignature
electrohydrodynamicSignature =
  mechanism-signature electrohydrodynamicForce false true false false false true true

woodwardSignature : MechanismSignature
woodwardSignature =
  mechanism-signature woodwardInertialVariation false true false true false true false

negativeMassSignature : MechanismSignature
negativeMassSignature =
  mechanism-signature negativeMassConstitutive false false false true true true false

metricEngineeringSignature : MechanismSignature
metricEngineeringSignature =
  mechanism-signature metricEngineering false false false false true false false

ordinarySignature : MechanismSignature
ordinarySignature =
  mechanism-signature ordinaryMechanicalOrEM false false false false false true true

------------------------------------------------------------------------
-- BIDI reverse acquisition cutset.
--
-- A downstream mechanism conclusion routes backward to receipts that can
-- distinguish a field effect from apparatus momentum transfer or inertia.
------------------------------------------------------------------------

record GravityMechanismBidiCutset : Set where
  constructor gravity-mechanism-bidi-cutset
  field
    freeFallTestRequiredForGravityClaim : Bool
    freeFallTestRequiredForGravityClaimIsTrue :
      freeFallTestRequiredForGravityClaim ≡ true

    externalTestMassRequiredForFieldClaim : Bool
    externalTestMassRequiredForFieldClaimIsTrue :
      externalTestMassRequiredForFieldClaim ≡ true

    momentumAccountingRequiredForThrustClaim : Bool
    momentumAccountingRequiredForThrustClaimIsTrue :
      momentumAccountingRequiredForThrustClaim ≡ true

    inertialComparisonRequiredForMassVariationClaim : Bool
    inertialComparisonRequiredForMassVariationClaimIsTrue :
      inertialComparisonRequiredForMassVariationClaim ≡ true

    phaseOnOffComparisonRequiredForCoherenceClaim : Bool
    phaseOnOffComparisonRequiredForCoherenceClaimIsTrue :
      phaseOnOffComparisonRequiredForCoherenceClaim ≡ true

    vacuumControlRequiredForIonWindExclusion : Bool
    vacuumControlRequiredForIonWindExclusionIsTrue :
      vacuumControlRequiredForIonWindExclusion ≡ true

canonicalGravityMechanismBidiCutset : GravityMechanismBidiCutset
canonicalGravityMechanismBidiCutset =
  gravity-mechanism-bidi-cutset
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Negative mass BIDI: reverse-route the phrase to a coordinate before asking
-- how it could be produced.
------------------------------------------------------------------------

data NegativeMassTarget : Set where
  higgsMassParameter : NegativeMassTarget
  inertialMass : NegativeMassTarget
  passiveGravitationalResponse : NegativeMassTarget
  activeGravitationalSource : NegativeMassTarget
  effectiveNegativePressureSource : NegativeMassTarget

record NegativeMassBidiBoundary : Set where
  constructor negative-mass-bidi-boundary
  field
    unspecifiedNegativeMassIsWellPosed : Bool
    unspecifiedNegativeMassIsWellPosedIsFalse :
      unspecifiedNegativeMassIsWellPosed ≡ false

    higgsManipulationAloneClosesMacroscopicNegativeMass : Bool
    higgsManipulationAloneClosesMacroscopicNegativeMassIsFalse :
      higgsManipulationAloneClosesMacroscopicNegativeMass ≡ false

    stressEnergyReceiptRequiredForActiveGravityClaim : Bool
    stressEnergyReceiptRequiredForActiveGravityClaimIsTrue :
      stressEnergyReceiptRequiredForActiveGravityClaim ≡ true

canonicalNegativeMassBidiBoundary : NegativeMassBidiBoundary
canonicalNegativeMassBidiBoundary =
  negative-mass-bidi-boundary false refl false refl true refl

------------------------------------------------------------------------
-- Commonality theorem shape: all exotic families are represented as proposed
-- departures from an ordinary constitutive/response map, but the departure
-- channel is not erased.
------------------------------------------------------------------------

record CommonMechanismKernel : Set where
  constructor common-mechanism-kernel
  field
    engineeredState : String
    ordinaryResponseMap : String
    proposedDeparture : H.DepartureChannel
    requiredResidual : String

liTorrKernel : CommonMechanismKernel
liTorrKernel = common-mechanism-kernel
  "superconducting/coherent phase plus electromagnetic excitation"
  "stress-energy and mass-current source ordinary weak-field gravity"
  H.coherentCurrentGravityCoupling
  "phase-correlated external gravity-channel residual after ordinary fields are removed"

woodwardKernel : CommonMechanismKernel
woodwardKernel = common-mechanism-kernel
  "accelerated time-dependent internal-energy configuration"
  "ordinary inertia and momentum conservation"
  H.inertialMassVariation
  "repeatable inertial/momentum residual after mechanical and EM exchange are closed"

metricKernel : CommonMechanismKernel
metricKernel = common-mechanism-kernel
  "engineered stress-energy configuration"
  "Einstein stress-energy to metric response"
  H.metricEngineering
  "metric/clock/geodesic signature consistent across independent probes"
