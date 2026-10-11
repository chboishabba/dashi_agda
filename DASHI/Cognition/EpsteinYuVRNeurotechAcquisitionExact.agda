module DASHI.Cognition.EpsteinYuVRNeurotechAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- GINO YU / EPSTEIN VR-EEG-CONSCIOUSNESS ACQUISITION
------------------------------------------------------------------------

data NeurotechSource : Set where
  kuhnAIConsciousnessThread : NeurotechSource
  viveHouseSetupThread : NeurotechSource
  viveForEpsteinFollowup : NeurotechSource

data NeurotechEdge : Set where
  aiConsciousnessInterest : NeurotechEdge
  eegIndustryExploration : NeurotechEdge
  vrHardwareAtResidence : NeurotechEdge
  vrWalkthroughOffer : NeurotechEdge

record NeurotechReceipt : Set where
  constructor neurotech-receipt
  field
    source : NeurotechSource
    efta : String
    edge : NeurotechEdge
    directlyDocumented : Bool
    performedAtEpsteinResidence : Bool
    experimentProtocolEstablished : Bool
    fmriUseEstablished : Bool
    behaviourPredictionEstablished : Bool
open NeurotechReceipt public

epsteinAIConsciousnessInterest : NeurotechReceipt
epsteinAIConsciousnessInterest = neurotech-receipt
  kuhnAIConsciousnessThread
  "EFTA00820667 / EFTA00820611 / EFTA02453148"
  aiConsciousnessInterest
  true false false false false

yuEEGIndustryExploration : NeurotechReceipt
yuEEGIndustryExploration = neurotech-receipt
  kuhnAIConsciousnessThread
  "EFTA00820667"
  eegIndustryExploration
  true false false false false

yuViveHouseSetup : NeurotechReceipt
yuViveHouseSetup = neurotech-receipt
  viveHouseSetupThread
  "EFTA00438160-EFTA00438162 / EFTA00438756-EFTA00438758"
  vrHardwareAtResidence
  true true false false false

yuViveForEpsteinFollowup : NeurotechReceipt
yuViveForEpsteinFollowup = neurotech-receipt
  viveForEpsteinFollowup
  "EFTA01059141 / EFTA01785592"
  vrWalkthroughOffer
  true false false false false

------------------------------------------------------------------------
-- PROMOTION FIREWALLS
------------------------------------------------------------------------

data VRSetupImpliesExperiment : Set where
data EEGInterestImpliesEEGStudy : Set where
data AIConsciousnessInterestImpliesMindControl : Set where
data VRHardwareImpliesBehaviourEngineering : Set where

vrSetupDoesNotEstablishExperiment : VRSetupImpliesExperiment → ⊥
vrSetupDoesNotEstablishExperiment ()

eegInterestDoesNotEstablishEEGStudy : EEGInterestImpliesEEGStudy → ⊥
eegInterestDoesNotEstablishEEGStudy ()

aiConsciousnessInterestDoesNotEstablishMindControl :
  AIConsciousnessInterestImpliesMindControl → ⊥
aiConsciousnessInterestDoesNotEstablishMindControl ()

vrHardwareDoesNotEstablishBehaviourEngineering :
  VRHardwareImpliesBehaviourEngineering → ⊥
vrHardwareDoesNotEstablishBehaviourEngineering ()

record EpsteinYuNeurotechBoundary : Set where
  constructor epstein-yu-neurotech-boundary
  field
    aiConsciousnessInterestPaid : Bool
    eegExplorationPaid : Bool
    viveAtResidencePaid : Bool
    specificExperimentPaid : Bool
    fmriHistoricalUsePaid : Bool
    behaviourPredictionPaid : Bool

canonicalEpsteinYuNeurotechBoundary : EpsteinYuNeurotechBoundary
canonicalEpsteinYuNeurotechBoundary =
  epstein-yu-neurotech-boundary true true true false false false
