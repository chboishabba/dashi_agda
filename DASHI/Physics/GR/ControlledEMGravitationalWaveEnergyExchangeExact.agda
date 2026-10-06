module DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.SignedGravitationalWaveCouplingBidiExact as SignedWave

------------------------------------------------------------------------
-- CONTROLLED EM <-> GRAVITATIONAL-WAVE ENERGY EXCHANGE
--
-- Source: Ralf Schützhold, "Stimulated Emission or Absorption of Gravitons by
-- Light", Phys. Rev. Lett. 135, 171501 (2025), DOI 10.1103/xd97-c6d7.
--
-- The source studies the standard linearised-GR h^{mu nu} T_{mu nu}
-- interaction for electromagnetic radiation in an extended Mach-Zehnder /
-- Sagnac geometry.  This module does NOT promote the proposal to observed
-- graviton exchange or antigravity.  It introduces the missing controlled
-- stress-energy-exchange stage between vacuum propagation and detector
-- projection and makes the sign/reversal obligations explicit.
------------------------------------------------------------------------

data ControlledWaveStage : Set where
  sourceGenerationStage : ControlledWaveStage
  vacuumPropagationStage : ControlledWaveStage
  controlledStressEnergyExchangeStage : ControlledWaveStage
  detectorProjectionStage : ControlledWaveStage

data CouplingSensitivity : Set where
  sourceCouplingSensitive : CouplingSensitivity
  propagationDoesNotIdentifySourceCoupling : CouplingSensitivity
  exchangeCouplingModelDependent : CouplingSensitivity
  projectionDoesNotIdentifySourceCoupling : CouplingSensitivity

controlledStageSensitivity : ControlledWaveStage → CouplingSensitivity
controlledStageSensitivity sourceGenerationStage = sourceCouplingSensitive
controlledStageSensitivity vacuumPropagationStage = propagationDoesNotIdentifySourceCoupling
controlledStageSensitivity controlledStressEnergyExchangeStage = exchangeCouplingModelDependent
controlledStageSensitivity detectorProjectionStage = projectionDoesNotIdentifySourceCoupling

------------------------------------------------------------------------
-- Same-object interaction carrier.
------------------------------------------------------------------------

record EMGWInteractionCarrier : Set₁ where
  constructor em-gw-interaction-carrier
  field
    MetricPerturbation : Set
    EMStressEnergy : Set
    OpticalPath : Set
    InteractionWork : Set
    EMFrequencyShift : Set
    EMPhaseShift : Set

    metricPerturbation : MetricPerturbation
    emStressEnergy : EMStressEnergy
    opticalPath : OpticalPath
    interactionWork : InteractionWork
    frequencyShift : EMFrequencyShift
    phaseShift : EMPhaseShift

    -- Physical/source receipts.  These fields are intentionally propositions
    -- supplied by a concrete GR/EM instantiation rather than postulated here.
    LinearisedGRInteractionReceipt : Set
    linearisedGRInteractionReceipt : LinearisedGRInteractionReceipt

    StressEnergyConservationReceipt : Set
    stressEnergyConservationReceipt : StressEnergyConservationReceipt

    WorkToFrequencyReceipt : Set
    workToFrequencyReceipt : WorkToFrequencyReceipt

    FrequencyToPhaseReceipt : Set
    frequencyToPhaseReceipt : FrequencyToPhaseReceipt

open EMGWInteractionCarrier public

------------------------------------------------------------------------
-- Reversal/refutation structure.
--
-- The controlled experiment is stronger than a one-shot strain observation:
-- geometry, GW phase and polarization can be reversed while retaining the
-- literal optical apparatus.  A physical instantiation must therefore provide
-- matched opposite-sign receipts rather than merely a non-zero output.
------------------------------------------------------------------------

data ExchangeReversal : Set where
  orthogonalPathExchange : ExchangeReversal
  halfCyclePhaseExchange : ExchangeReversal
  polarizationExchange : ExchangeReversal

data ExchangeSign : Set where
  emissionLike : ExchangeSign
  absorptionLike : ExchangeSign
  zeroExchange : ExchangeSign

record ControlledExchangeReversalReceipt : Set₁ where
  constructor controlled-exchange-reversal-receipt
  field
    carrier : EMGWInteractionCarrier
    reversal : ExchangeReversal
    before : ExchangeSign
    after : ExchangeSign

    SamePhysicalOpticalSystem : Set
    samePhysicalOpticalSystem : SamePhysicalOpticalSystem

    OppositeExchangeReceipt : Set
    oppositeExchangeReceipt : OppositeExchangeReceipt

open ControlledExchangeReversalReceipt public

------------------------------------------------------------------------
-- Quantum branch firewall.
--
-- Quantised energy accounting or non-classical photon sensitivity is not by
-- itself a proof that the gravitational field is quantised.  The latter needs
-- an independently discriminating state-overlap / entanglement / visibility
-- receipt.
------------------------------------------------------------------------

data GravityQuantisationStatus : Set where
  classicalEnergyExchangeCompatible : GravityQuantisationStatus
  quantumEnergyAccountingCompatible : GravityQuantisationStatus
  quantumGravityDiscriminatorRequired : GravityQuantisationStatus

record QuantumExchangeBoundary : Set where
  constructor quantum-exchange-boundary
  field
    integerHbarOmegaAccountingAloneProvesQuantisedGravity : Bool
    nonclassicalPhotonsMayImproveSensitivity : Bool
    opticalVisibilityMayProbeGravityStateOverlap : Bool
    gravityStateDiscriminatorStillRequired : Bool

canonicalQuantumExchangeBoundary : QuantumExchangeBoundary
canonicalQuantumExchangeBoundary =
  quantum-exchange-boundary false true true true

------------------------------------------------------------------------
-- Cross-check against the pre-existing signed-wave boundary.
--
-- We deliberately import the existing source/propagation/projection theorem
-- instead of replacing it.  Its key result remains: vacuum propagation alone
-- does not identify the sign of the matter coupling.  The new exchange stage
-- is the controlled place where competing coupling models may differ.
------------------------------------------------------------------------

existingSignedWaveBoundary : SignedWave.SignedGravitationalWaveBoundary
existingSignedWaveBoundary = SignedWave.canonicalSignedGravitationalWaveBoundary

record ControlledExchangeBoundary : Set where
  constructor controlled-exchange-boundary
  field
    sourceGenerationDistinctFromVacuumPropagation : Bool
    controlledExchangeDistinctFromDetectorProjection : Bool
    vacuumPropagationAloneIdentifiesMatterCouplingSign : Bool
    controlledExchangeMayDiscriminateCouplingModels : Bool
    reversalReceiptsRequiredForSignClaim : Bool
    conservationReceiptRequiredForEnergyTransferClaim : Bool
    opticalReadoutAloneProvesGravitonQuantisation : Bool
    controlledExchangeAloneProvesAntigravity : Bool

canonicalControlledExchangeBoundary : ControlledExchangeBoundary
canonicalControlledExchangeBoundary =
  controlled-exchange-boundary true true false true true true false false
