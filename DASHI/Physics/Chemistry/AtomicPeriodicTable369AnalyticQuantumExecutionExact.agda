module DASHI.Physics.Chemistry.AtomicPeriodicTable369AnalyticQuantumExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as C3

------------------------------------------------------------------------
-- Source/authority receipts for the analytic execution layer.
--
-- These sources supply standard mathematical/atomic-spectroscopy formulas.
-- They do not supply or validate a DASHI ternary-to-atom identity.
------------------------------------------------------------------------

record AnalyticAtomicSourceReceipt : Set where
  constructor analyticAtomicSourceReceipt
  field
    authority : String
    locator : String
    sourceRole : String
    relationship : String

open AnalyticAtomicSourceReceipt public

hydrogenicDLMFReceipt : AnalyticAtomicSourceReceipt
hydrogenicDLMFReceipt =
  analyticAtomicSourceReceipt
    "NIST Digital Library of Mathematical Functions"
    "DLMF §18.39(ii), Hydrogen Atom"
    "mathematical/physics reference for normalized Coulomb-Laguerre hydrogenic bound states"
    "supplies the analytic hydrogenic execution donor; does not identify a ternary state with an orbital"

nistE1Receipt : AnalyticAtomicSourceReceipt
nistE1Receipt =
  analyticAtomicSourceReceipt
    "NIST Atomic Spectroscopy"
    "Spectral Lines: Selection Rules, Intensities, Transition Probabilities, Values, and Line Strengths"
    "atomic-spectroscopy reference for conventional electric-dipole selection rules"
    "supplies the allowed one-electron E1 transition surface; does not supply measured line-intensity data for the DASHI fixture"

------------------------------------------------------------------------
-- The same p-shell carrier contains two different C3 operations.
--
-- Spatial C3 rotation is diagonal in the magnetic basis: it leaves the basis
-- label fixed and contributes the already-owned symbolic character phase.
-- Charge +1 transport changes the magnetic-sector label cyclically.
------------------------------------------------------------------------

data MagneticC3Operation : Set where
  spatialRotation120 : MagneticC3Operation
  positiveChargeTransport : MagneticC3Operation

basisStateAction : MagneticC3Operation -> C3.MagneticState -> C3.MagneticState
basisStateAction spatialRotation120 m = m
basisStateAction positiveChargeTransport m = C3.chargePositiveStep m

basisPhaseAction : MagneticC3Operation -> C3.MagneticState -> C3.C3Phase
basisPhaseAction spatialRotation120 m = C3.rotationPhase m
basisPhaseAction positiveChargeTransport m = C3.phaseNeutral

spatialRotationFixesZeroBasisState :
  basisStateAction spatialRotation120 C3.mZero ≡ C3.mZero
spatialRotationFixesZeroBasisState = refl

chargeTransportMovesZeroBasisState :
  basisStateAction positiveChargeTransport C3.mZero ≡ C3.mPosOne
chargeTransportMovesZeroBasisState = refl

spatialRotationHasPositivePhaseOnMPosOne :
  basisPhaseAction spatialRotation120 C3.mPosOne ≡ C3.phasePositive
spatialRotationHasPositivePhaseOnMPosOne = refl

------------------------------------------------------------------------
-- Numerical producer provenance.  The Python script independently evaluates
-- the standard analytic hydrogenic formulas and the finite three-state action.
------------------------------------------------------------------------

analyticExecutionProducer : String
analyticExecutionProducer = "scripts/atomic_quantum_369_visualization.py"

record AnalyticQuantumExecutionBoundary : Set where
  constructor analyticQuantumExecutionBoundary
  field
    finitePShellC3SameActionAlreadyOwned : Bool
    analyticHydrogenicWavefunctionsExecuted : Bool
    spatialC3RotationResidualExecuted : Bool
    weightedHydrogenicE1GraphExecuted : Bool
    lithiumBerylliumMinimalBasisSCFExecuted : Bool
    spatialRotationEqualsChargeTransport : Bool
    finiteC3RecognitionEqualsFullAtomic369Identity : Bool
    hydrogenicExecutionEqualsManyElectronRecovery : Bool
    E1SelectionRuleEqualsMeasuredTransitionIntensity : Bool
    lithiumBerylliumCompleteBasisRecoveryPaid : Bool

open AnalyticQuantumExecutionBoundary public

canonicalAnalyticQuantumExecutionBoundary : AnalyticQuantumExecutionBoundary
canonicalAnalyticQuantumExecutionBoundary =
  analyticQuantumExecutionBoundary
    true true true true true
    false false false false false

spatialRotationEqualsChargeTransportIsFalse :
  spatialRotationEqualsChargeTransport canonicalAnalyticQuantumExecutionBoundary ≡ false
spatialRotationEqualsChargeTransportIsFalse = refl

finiteC3RecognitionEqualsFullAtomic369IdentityIsFalse :
  finiteC3RecognitionEqualsFullAtomic369Identity canonicalAnalyticQuantumExecutionBoundary ≡ false
finiteC3RecognitionEqualsFullAtomic369IdentityIsFalse = refl

lithiumBerylliumMinimalBasisSCFExecutedIsTrue :
  lithiumBerylliumMinimalBasisSCFExecuted canonicalAnalyticQuantumExecutionBoundary ≡ true
lithiumBerylliumMinimalBasisSCFExecutedIsTrue = refl

lithiumBerylliumCompleteBasisRecoveryPaidIsFalse :
  lithiumBerylliumCompleteBasisRecoveryPaid canonicalAnalyticQuantumExecutionBoundary ≡ false
lithiumBerylliumCompleteBasisRecoveryPaidIsFalse = refl
