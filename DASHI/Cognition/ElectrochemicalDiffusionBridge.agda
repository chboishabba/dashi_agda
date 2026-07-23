module DASHI.Cognition.ElectrochemicalDiffusionBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Cognition.CognitiveResearchSources as Sources
import DASHI.Cognition.PsychedelicNetworkDiffusion as Network

------------------------------------------------------------------------
-- Physical communication is heterogeneous.
--
-- Axonal action-potential propagation, vesicular synaptic transmission,
-- gap-junction current, extracellular transmitter diffusion, and fMRI-derived
-- statistical dependence are not one literal wire protocol.  The finite bridge
-- below represents an extracellular concentration-gradient step separately
-- from the graph/effective-connectivity diffusion used in the network module.
--
-- Volume-transmission sources:
-- Fuxe et al. (2010), DOI 10.1016/j.pneurobio.2009.10.012.
-- Borroto-Escuela et al. (2015), DOI 10.1098/rstb.2014.0183.
------------------------------------------------------------------------

physicalDiffusionSources : List Sources.ResearchSource
physicalDiffusionSources =
  Sources.fuxeWiredAndVolumeTransmission ∷
  Sources.borrotoEscuelaVolumeTransmission ∷ []

data PhysicalPropagation : Set where
  voltageGatedAxonalPropagation
  vesicularReleaseAndReceptorBinding
  gapJunctionCurrent
  extracellularConcentrationDiffusion : PhysicalPropagation

record TwoCompartmentConcentration : Set where
  constructor concentration2
  field
    leftConcentration  : Nat
    rightConcentration : Nat

open TwoCompartmentConcentration public

totalConcentration : TwoCompartmentConcentration → Nat
totalConcentration state =
  leftConcentration state + rightConcentration state

concentrationGradient : TwoCompartmentConcentration → Nat
concentrationGradient state =
  Network.absDiff
    (leftConcentration state)
    (rightConcentration state)

-- One finite conservative flux step from the higher left compartment to the
-- lower right compartment.

initialConcentration : TwoCompartmentConcentration
initialConcentration = concentration2 5 1

afterOneDiffusiveFlux : TwoCompartmentConcentration
afterOneDiffusiveFlux = concentration2 4 2

initialTotalIsSix : totalConcentration initialConcentration ≡ 6
initialTotalIsSix = refl

afterFluxTotalIsSix : totalConcentration afterOneDiffusiveFlux ≡ 6
afterFluxTotalIsSix = refl

initialGradientIsFour : concentrationGradient initialConcentration ≡ 4
initialGradientIsFour = refl

afterFluxGradientIsTwo : concentrationGradient afterOneDiffusiveFlux ≡ 2
afterFluxGradientIsTwo = refl

record ConservativeDiffusionReceipt : Set where
  constructor conservativeDiffusionReceipt
  field
    before : TwoCompartmentConcentration
    after  : TwoCompartmentConcentration
    beforeTotal : Nat
    afterTotal  : Nat
    beforeGradient : Nat
    afterGradient  : Nat
    beforeTotalExact : totalConcentration before ≡ beforeTotal
    afterTotalExact : totalConcentration after ≡ afterTotal
    beforeGradientExact : concentrationGradient before ≡ beforeGradient
    afterGradientExact : concentrationGradient after ≡ afterGradient

canonicalConservativeDiffusion : ConservativeDiffusionReceipt
canonicalConservativeDiffusion = conservativeDiffusionReceipt
  initialConcentration
  afterOneDiffusiveFlux
  6
  6
  4
  2
  refl
  refl
  refl
  refl

------------------------------------------------------------------------
-- Observation/abstraction bridge.
--
-- A measured or hypothesised physical flux may contribute to an effective
-- cross-system edge, but the abstraction is not an identity: molecular
-- concentration, neuronal current, statistical functional connectivity and a
-- graph diffusion coefficient remain differently typed quantities.
------------------------------------------------------------------------

record PhysicalToNetworkTransport : Set where
  constructor physicalToNetworkTransport
  field
    physicalChannel : PhysicalPropagation
    physicalFluxCode : Nat
    effectiveCrossEdgeCode : Nat

volumeTransmissionToEffectiveEdge : PhysicalToNetworkTransport
volumeTransmissionToEffectiveEdge = physicalToNetworkTransport
  extracellularConcentrationDiffusion
  1
  1

record DiffusionLayerBoundary : Set where
  constructor diffusionLayerBoundary
  field
    physicalDiffusionModelled : Set
    networkTransportModelled  : Set
    layersIdentified          : Set

canonicalLayerBoundary : DiffusionLayerBoundary
canonicalLayerBoundary = diffusionLayerBoundary
  ConservativeDiffusionReceipt
  Network.TwoSystemProfile
  (0 ≡ 1)
