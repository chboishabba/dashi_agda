module DASHI.Chemistry.SpeciesMethodDetectionCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Chemistry.AssayDetectionEnvelopeExact as Detection

------------------------------------------------------------------------
-- SPECIES x METHOD x MATRIX DETECTION CROSS-POLLINATION
--
-- TransitionKernel owns solver-neutral chemical Species with identity, phase,
-- charge/composition and optical-role coordinates.  AssayDetectionEnvelopeExact
-- owns method-relative LOD/LOQ and readout coordinates.  This module welds the
-- two without pretending that molecular identity alone fixes detectability.
--
-- The same general measurement architecture appears in atomic/quantum
-- experiments elsewhere in the repository: carrier -> physical interaction ->
-- amplified/read-out signal -> calibration -> decision.  Structural reuse does
-- not identify chromatographic/MS chemistry with an atomic-qubit experiment.
------------------------------------------------------------------------

data SignalMechanism : Set where
  electronImpactIonisation
  electrosprayIonisation
  atmosphericPressureChemicalIonisation
  opticalAbsorption
  fluorescenceReadout
  otherValidatedSignalMechanism
  : SignalMechanism

data ResponseStatus : Set where
  responseValidated
  responseSuppressedOrBelowEnvelope
  responseUnresolved
  : ResponseStatus

record SpeciesMethodDetectionReceipt (species : Chemistry.Species) : Set where
  constructor speciesMethodDetectionReceipt
  field
    methodReceipt : Detection.MethodDetectionReceipt
    signalMechanism : SignalMechanism
    responseStatus : ResponseStatus

    -- Exact identity weld between the chemistry carrier and the analytical
    -- method's declared analyte coordinate.
    analyteIdentityWeld :
      Chemistry.speciesId species ≡ Detection.analyteReference methodReceipt

    phaseCompatibilityReference : String
    compositionOrFragmentReference : String
    chargeAdductReference : String
    transitionOrSpectrumReference : String
    recoveryReference : String
    interferenceReference : String

open SpeciesMethodDetectionReceipt public

------------------------------------------------------------------------
-- Finite regressions: same nominal molecule does not determine detectability,
-- and same method family does not determine an LOD/LOQ envelope.
------------------------------------------------------------------------

data SyntheticMoleculeIdentity : Set where
  sameMolecule : SyntheticMoleculeIdentity

data DetectionContext : Set where
  responsiveMatrixContext suppressedMatrixContext : DetectionContext

data ContextObservation : Set where
  reliableResponse noReliableResponse : ContextObservation

data ThresholdCode : Set where
  lowerThreshold higherThreshold : ThresholdCode

moleculeIdentity : DetectionContext → SyntheticMoleculeIdentity
moleculeIdentity _ = sameMolecule

contextObservation : DetectionContext → ContextObservation
contextObservation responsiveMatrixContext = reliableResponse
contextObservation suppressedMatrixContext = noReliableResponse

sameMoleculeDifferentDetection :
  NonFactor.NonFactorabilityWitness moleculeIdentity contextObservation
sameMoleculeDifferentDetection =
  NonFactor.nonFactorabilityWitness
    responsiveMatrixContext
    suppressedMatrixContext
    refl
    (λ ())

moleculeIdentityCannotRecoverMethodDetectability :
  NonFactor.FactorsThrough moleculeIdentity contextObservation → ⊥
moleculeIdentityCannotRecoverMethodDetectability =
  NonFactor.witnessRulesOutEveryFlatFactorisation sameMoleculeDifferentDetection

data MethodMatrixPair : Set where
  moleculeMatrixA moleculeMatrixB : MethodMatrixPair

methodFamilyProjection : MethodMatrixPair → Detection.MethodFamily
methodFamilyProjection _ = Detection.liquidChromatographyMassSpectrometry

thresholdForPair : MethodMatrixPair → ThresholdCode
thresholdForPair moleculeMatrixA = lowerThreshold
thresholdForPair moleculeMatrixB = higherThreshold

sameMethodFamilyDifferentThresholdEnvelope :
  NonFactor.NonFactorabilityWitness methodFamilyProjection thresholdForPair
sameMethodFamilyDifferentThresholdEnvelope =
  NonFactor.nonFactorabilityWitness
    moleculeMatrixA
    moleculeMatrixB
    refl
    (λ ())

methodFamilyAloneCannotRecoverDetectionThreshold :
  NonFactor.FactorsThrough methodFamilyProjection thresholdForPair → ⊥
methodFamilyAloneCannotRecoverDetectionThreshold =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    sameMethodFamilyDifferentThresholdEnvelope

------------------------------------------------------------------------
-- Absence from one signal channel also does not close all physically available
-- channels.  Orthogonal methods are genuine observation refinements only when
-- they have their own analyte/matrix validation receipts.
------------------------------------------------------------------------

data OneChannelNonresponseImpliesAllChannelsNonresponsePermission : Set where
data MolecularIdentityImpliesUniversalLODPermission : Set where

oneChannelNonresponseCannotAutoPromoteToAllChannels :
  OneChannelNonresponseImpliesAllChannelsNonresponsePermission → ⊥
oneChannelNonresponseCannotAutoPromoteToAllChannels ()

molecularIdentityCannotAutoPromoteToUniversalLOD :
  MolecularIdentityImpliesUniversalLODPermission → ⊥
molecularIdentityCannotAutoPromoteToUniversalLOD ()

record SpeciesMethodDetectionBoundary : Set where
  constructor speciesMethodDetectionBoundary
  field
    sameMoleculeMeansSameDetectionInEveryMatrix : Bool
    sameMethodFamilyMeansSameLODForEveryMolecule : Bool
    speciesIdentityAndMethodReceiptRequireExplicitWeld : Bool
    orthogonalReadoutCanAddInformationWhenValidated : Bool
    atomicQuantumReadoutAndPesticideAssayAreSameMechanism : Bool

canonicalSpeciesMethodDetectionBoundary : SpeciesMethodDetectionBoundary
canonicalSpeciesMethodDetectionBoundary =
  speciesMethodDetectionBoundary false false true true false
