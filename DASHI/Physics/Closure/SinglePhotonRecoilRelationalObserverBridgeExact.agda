module DASHI.Physics.Closure.SinglePhotonRecoilRelationalObserverBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.RelationalObserverGainExact as Gain
import DASHI.Physics.Foundations.PathIntegralExperimentalSourceRegistryExact as Sources
import DASHI.Physics.Foundations.TrajectoryProjectionCausticExact as Caustic
import DASHI.Physics.Closure.TSFVBidirectionalCausticBridgeExact as TSFVCaustic

------------------------------------------------------------------------
-- Source-bounded finite shadow of Wu et al. 2026:
--
-- photon absorption
--   -> molecular recoil
--   -> shared motional displacement
--   -> relational/geometric phase sensitivity
--   -> atomic-qubit readout.
--
-- The physical recoil is not enlarged by the observer.  Instead, the
-- observer geometry makes the small perturbation more discriminable.
------------------------------------------------------------------------

data MolecularInternalState : Set where
  internalGround : MolecularInternalState
  internalExcited : MolecularInternalState

data SharedMotionState : Set where
  undisplacedMotion : SharedMotionState
  photonRecoiledMotion : SharedMotionState

data LogicQubitReadout : Set where
  qubitBaseline : LogicQubitReadout
  qubitPhaseRotated : LogicQubitReadout

data DirectRecoilReadout : Set where
  directRecoilUnresolved : DirectRecoilReadout

data CoupledExperimentalState : Set where
  beforeAbsorption : CoupledExperimentalState
  afterAbsorption : CoupledExperimentalState

data MolecularPerturbationPair : Set where
  absorbedPhotonPair : MolecularPerturbationPair

data DirectIndistinguishable : MolecularPerturbationPair → Set where
  directReadoutCannotResolveToyRecoil :
    DirectIndistinguishable absorbedPhotonPair

data RelationalDistinguishable : MolecularPerturbationPair → Set where
  catPhaseReadoutSeparatesToyRecoil :
    RelationalDistinguishable absorbedPhotonPair

molecularObserverGain : Gain.RelationalObserverGain
molecularObserverGain =
  record
    { FineState = CoupledExperimentalState
    ; CoarseObservation = DirectRecoilReadout
    ; RefinedObservation = LogicQubitReadout
    ; coarseObserve = λ _ → directRecoilUnresolved
    ; refinedObserve = λ
        { beforeAbsorption → qubitBaseline
        ; afterAbsorption → qubitPhaseRotated
        }
    ; PerturbationPair = MolecularPerturbationPair
    ; unperturbed = λ _ → beforeAbsorption
    ; perturbed = λ _ → afterAbsorption
    ; coarseIndistinguishable = DirectIndistinguishable
    ; refinedDistinguishable = RelationalDistinguishable
    ; gainReading =
        "Finite shadow of the single-molecule recoil experiment: the recoil remains small, while a cat-state-assisted relational phase observer maps it to a distinguishable logic-qubit readout."
    }

molecularObserverGainWitness : Gain.ObserverGainWitness molecularObserverGain
molecularObserverGainWitness =
  record
    { pair = absorbedPhotonPair
    ; coarseWitness = directReadoutCannotResolveToyRecoil
    ; refinedWitness = catPhaseReadoutSeparatesToyRecoil
    }

refinedReadoutSeparatesAbsorptionToyStates :
  Gain.refinedObserve molecularObserverGain beforeAbsorption
  ≡
  Gain.refinedObserve molecularObserverGain afterAbsorption
  → ⊥
refinedReadoutSeparatesAbsorptionToyStates ()

------------------------------------------------------------------------
-- Keep coupling, entanglement, displacement, phase sensitivity, and readout
-- as distinct roles.  The experiment warrants entanglement at the stated
-- qubit--motion layer, not as a synonym for every contextual relation.
------------------------------------------------------------------------

data RelationalPhysicsLayer : Set where
  coulombCouplingLayer : RelationalPhysicsLayer
  sharedNormalModeLayer : RelationalPhysicsLayer
  qubitMotionEntanglementLayer : RelationalPhysicsLayer
  recoilDisplacementLayer : RelationalPhysicsLayer
  geometricPhaseLayer : RelationalPhysicsLayer
  logicReadoutLayer : RelationalPhysicsLayer

------------------------------------------------------------------------
-- Compression/amplification duality.
--
-- Caustic side: several fine histories -> one sharp coarse observation.
-- Recoil side: one small fine residual -> increased coarse discriminability.
------------------------------------------------------------------------

data FineCoarseMechanism : Set where
  manyFineToOneSharpCoarse : FineCoarseMechanism
  tinyFineResidualToCoarseSeparation : FineCoarseMechanism

compressionMechanism : FineCoarseMechanism
compressionMechanism = manyFineToOneSharpCoarse

amplificationMechanism : FineCoarseMechanism
amplificationMechanism = tinyFineResidualToCoarseSeparation

compressionAndAmplificationAreDistinct :
  compressionMechanism ≡ amplificationMechanism → ⊥
compressionAndAmplificationAreDistinct ()

record SinglePhotonRecoilRelationalObserverBridge : Set₁ where
  field
    source : Sources.SourceReference
    observerGainSurface : Gain.RelationalObserverGain
    observerGainWitness : Gain.ObserverGainWitness observerGainSurface
    gainBoundary : Gain.RelationalObserverGainBoundary

    tsfvCausticSurface : TSFVCaustic.TSFVBidirectionalCausticBridge

    experimentallyWarrantedQubitMotionEntanglement : Bool
    experimentallyWarrantedQubitMotionEntanglementIsTrue :
      experimentallyWarrantedQubitMotionEntanglement ≡ true

    observerAmplificationIncreasesPhotonRecoil : Bool
    observerAmplificationIncreasesPhotonRecoilIsFalse :
      observerAmplificationIncreasesPhotonRecoil ≡ false

    coulombCouplingMeansEntanglementByDefinition : Bool
    coulombCouplingMeansEntanglementByDefinitionIsFalse :
      coulombCouplingMeansEntanglementByDefinition ≡ false

    recoilExperimentValidatesTSFV : Bool
    recoilExperimentValidatesTSFVIsFalse :
      recoilExperimentValidatesTSFV ≡ false

    modelIsCompleteAbsoluteAbsorptionTheory : Bool
    modelIsCompleteAbsoluteAbsorptionTheoryIsFalse :
      modelIsCompleteAbsoluteAbsorptionTheory ≡ false

    bridgeReading : String

open SinglePhotonRecoilRelationalObserverBridge public

canonicalSinglePhotonRecoilRelationalObserverBridge :
  SinglePhotonRecoilRelationalObserverBridge
canonicalSinglePhotonRecoilRelationalObserverBridge =
  record
    { source = Sources.wuEtAl2026MolecularRecoil
    ; observerGainSurface = molecularObserverGain
    ; observerGainWitness = molecularObserverGainWitness
    ; gainBoundary = Gain.canonicalRelationalObserverGainBoundary
    ; tsfvCausticSurface = TSFVCaustic.canonicalTSFVBidirectionalCausticBridge
    ; experimentallyWarrantedQubitMotionEntanglement = true
    ; experimentallyWarrantedQubitMotionEntanglementIsTrue = refl
    ; observerAmplificationIncreasesPhotonRecoil = false
    ; observerAmplificationIncreasesPhotonRecoilIsFalse = refl
    ; coulombCouplingMeansEntanglementByDefinition = false
    ; coulombCouplingMeansEntanglementByDefinitionIsFalse = refl
    ; recoilExperimentValidatesTSFV = false
    ; recoilExperimentValidatesTSFVIsFalse = refl
    ; modelIsCompleteAbsoluteAbsorptionTheory = false
    ; modelIsCompleteAbsoluteAbsorptionTheoryIsFalse = refl
    ; bridgeReading =
        "Wu et al. provide an experimental instance of relational observer amplification: single-photon recoil remains microscopically small while shared motion plus qubit-motion entanglement and phase-sensitive readout make the recoil distinguishable.  This complements caustic compression without validating TSFV."
    }
