module DASHI.Cognition.HardtOptogeneticNobelCausalCutExact where

-- Nobel-linked optogenetic causal PROVENANCE, not Nobel-authored mathematics.
-- Hegemann/Nagel channelrhodopsin; Deisseroth neuronal application:
-- 2026 Nobel Prize in Physiology or Medicine, announced 2026-10-05.
-- Original optical engram sources: Liu et al. (2012) DOI
-- 10.1038/nature11028 and Ramirez et al. (2013) DOI
-- 10.1126/science.1239073.
-- Inter-areal two-photon holographic source: Abdeladim et al. (2026)
-- Nature Neuroscience DOI 10.1038/s41593-026-02350-9.
-- Actual optics/neural source owner: sibling diamond PR #1238
-- Biology.OptogeneticMemoryObservationBoundaryExact (not imported;
-- stacked PR #1252 cannot assume a merge from its sibling branch).
--
-- FINITE MODEL ONLY: no experimental human neural field, photocurrent,
-- molecular kinetics, mind-reading, inter-person influence or proof
-- of a paranormal or historical claim.

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
import DASHI.Core.CoarseFineFabricCalculusExact as Fabric

------------------------------------------------------------------------
-- Two physically distinct mechanisms can agree on a successful optical
-- stimulation trial. The missing expression-negative light-only control
-- is mathematically indispensable to distinguish these TWO models.
------------------------------------------------------------------------

data OpticalMechanism : Set where
  lightGatedOpsin : OpticalMechanism
  illuminationPickup : OpticalMechanism

-- A finite "positive" physiological readout.  True means a reported
-- response, not a measured current or other physical scale.
response : OpticalMechanism → Bool → Bool → Bool
response lightGatedOpsin true true = true
response lightGatedOpsin true false = false
response lightGatedOpsin false true = false
response lightGatedOpsin false false = false
response illuminationPickup true true = true
response illuminationPickup true false = false
response illuminationPickup false true = true
response illuminationPickup false false = false

-- Ordered inputs: illumination present, opsin expressed.
activeObservation : OpticalMechanism → Bool
activeObservation m = response m true true

expressionNegativeControl : OpticalMechanism → Bool
expressionNegativeControl m = response m true false

activeSame :
  activeObservation lightGatedOpsin ≡
  activeObservation illuminationPickup
activeSame = refl

expressionNegativeDiffers :
  expressionNegativeControl lightGatedOpsin ≡
  expressionNegativeControl illuminationPickup → ⊥
expressionNegativeDiffers ()

lightOnlyCollision :
  Fabric.ProjectionCollision activeObservation expressionNegativeControl
lightOnlyCollision = record
  { Fabric.ProjectionCollision.left = lightGatedOpsin
  ; Fabric.ProjectionCollision.right = illuminationPickup
  ; Fabric.ProjectionCollision.sameProjection = activeSame
  ; Fabric.ProjectionCollision.consumerSeparates = expressionNegativeDiffers
  }

noUniversalLightOnlyPredictionFromActive :
  (decoder : Bool → Bool) →
  ((m : OpticalMechanism) →
     expressionNegativeControl m ≡ decoder (activeObservation m)) → ⊥
noUniversalLightOnlyPredictionFromActive =
  Fabric.consumerCannotFactorThroughProjection lightOnlyCollision

------------------------------------------------------------------------
-- Separate downstream physiology from direct light/recording pickup.
-- Both fit the *unblocked* stimulation, while only a physically
-- network-mediated output is changed by a declared synaptic blocker.
-- This is a conceptual mechanism test, NOT a real blocking protocol.
------------------------------------------------------------------------

data DownstreamMechanism : Set where
  ordinaryNeuralPropagation : DownstreamMechanism
  directOpticalReadoutArtifact : DownstreamMechanism

downstreamReadout : DownstreamMechanism → Bool → Bool
downstreamReadout ordinaryNeuralPropagation false = true
downstreamReadout ordinaryNeuralPropagation true = false
downstreamReadout directOpticalReadoutArtifact false = true
downstreamReadout directOpticalReadoutArtifact true = true

unblockedReadout : DownstreamMechanism → Bool
unblockedReadout m = downstreamReadout m false

blockerConditionReadout : DownstreamMechanism → Bool
blockerConditionReadout m = downstreamReadout m true

sameUnblockedResponse :
  unblockedReadout ordinaryNeuralPropagation ≡
  unblockedReadout directOpticalReadoutArtifact
sameUnblockedResponse = refl

differentBlockedResponse :
  blockerConditionReadout ordinaryNeuralPropagation ≡
  blockerConditionReadout directOpticalReadoutArtifact → ⊥
differentBlockedResponse ()

downstreamCollision :
  Fabric.ProjectionCollision unblockedReadout blockerConditionReadout
downstreamCollision = record
  { Fabric.ProjectionCollision.left = ordinaryNeuralPropagation
  ; Fabric.ProjectionCollision.right = directOpticalReadoutArtifact
  ; Fabric.ProjectionCollision.sameProjection = sameUnblockedResponse
  ; Fabric.ProjectionCollision.consumerSeparates = differentBlockedResponse
  }

noUniversalBlockedResponseFromActive :
  (decoder : Bool → Bool) →
  ((m : DownstreamMechanism) →
     blockerConditionReadout m ≡ decoder (unblockedReadout m)) → ⊥
noUniversalBlockedResponseFromActive =
  Fabric.consumerCannotFactorThroughProjection downstreamCollision

------------------------------------------------------------------------
-- Explicit evidence boundaries, all unavailable here.
------------------------------------------------------------------------

data ActualOpticalDoseAndOpsinExpressionReceipt : Set where
data SourceMatchedNeuralRecordingReceipt : Set where
data ControlledDownstreamAndShamReceipt : Set where

record NobelOptogeneticsExperimentalPromotion : Set where
  field
    actualDose : ActualOpticalDoseAndOpsinExpressionReceipt
    neuralState : SourceMatchedNeuralRecordingReceipt
    causalOutput : ControlledDownstreamAndShamReceipt
