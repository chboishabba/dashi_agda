module DASHI.Biology.FiveHT2ARecognitionStateSpaceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Kluver5HT2AMolecularProteinInstantiationExact as Molecular
import DASHI.Biology.FiveHT2ASignalingDialecticExact as Signaling
import DASHI.Biology.TargetIndexedRecognitionGeometryExact as Geometry
import DASHI.Biology.ContextIndexedRecognitionGeometryExact as Context

------------------------------------------------------------------------
-- 5-HT2A RECOGNITION STATE SPACE
--
-- The relevant state is not "the molecule" alone.  This finite typed surface
-- keeps distinct:
--
--   ligand identity
--   target / receptor context
--   target-relative mismatch
--   signaling profile
--   downstream interpretation boundary.
------------------------------------------------------------------------

record FiveHT2ARecognitionState : Set where
  constructor fiveHT2ARecognitionState
  field
    ligand : Molecular.MolecularIdentityReceipt
    targetState : Context.ContextIndexedRecognitionTarget
    mismatch : Geometry.RecognitionMismatch
    signaling : Signaling.SignalingProfile

    stateReference : String

open FiveHT2ARecognitionState public

canonicalLSDState0 : FiveHT2ARecognitionState
canonicalLSDState0 =
  fiveHT2ARecognitionState
    Molecular.lsdIdentity
    Context.targetInContext0
    Geometry.canonicalPairMismatch
    Signaling.lsdSignalingProfile
    "finite LSD recognition state in permissive receptor-context fixture"

canonicalLSDState1 : FiveHT2ARecognitionState
canonicalLSDState1 =
  fiveHT2ARecognitionState
    Molecular.lsdIdentity
    Context.targetInContext1
    Geometry.canonicalPairMismatch
    Signaling.lsdSignalingProfile
    "finite LSD recognition state in strict receptor-context fixture"

state0Admitted :
  Context.AdmittedInContext
    (targetState canonicalLSDState0)
    (mismatch canonicalLSDState0)
state0Admitted =
  Context.canonicalPairAdmittedInContext0

state1Rejected :
  Context.AdmittedInContext
    (targetState canonicalLSDState1)
    (mismatch canonicalLSDState1)
  →
  ⊥
state1Rejected =
  Context.canonicalPairRejectedInContext1

------------------------------------------------------------------------
-- Same ligand and mismatch, changed target context.
------------------------------------------------------------------------

sameLigandAcrossFixtureStates :
  MolecularIdentityReceipt
    (ligand canonicalLSDState0)
  ≡
  MolecularIdentityReceipt
    (ligand canonicalLSDState1)
sameLigandAcrossFixtureStates = refl

sameMismatchAcrossFixtureStates :
  mismatch canonicalLSDState0
  ≡
  mismatch canonicalLSDState1
sameMismatchAcrossFixtureStates = refl

record ContextDependentRecognitionWitness : Set where
  constructor contextDependentRecognitionWitness
  field
    first second : FiveHT2ARecognitionState

    sameLigandIdentity : Bool
    sameLigandIdentityIsTrue :
      sameLigandIdentity ≡ true

    samePairMismatch : Bool
    samePairMismatchIsTrue :
      samePairMismatch ≡ true

    firstAdmitted :
      Context.AdmittedInContext
        (targetState first)
        (mismatch first)

    secondRejected :
      Context.AdmittedInContext
        (targetState second)
        (mismatch second)
      →
      ⊥

open ContextDependentRecognitionWitness public

canonicalContextDependentRecognitionWitness :
  ContextDependentRecognitionWitness
canonicalContextDependentRecognitionWitness =
  contextDependentRecognitionWitness
    canonicalLSDState0
    canonicalLSDState1
    true refl
    true refl
    state0Admitted
    state1Rejected

------------------------------------------------------------------------
-- State-space projections.
------------------------------------------------------------------------

data FiveHT2AStateAxis : Set where
  ligandIdentityAxis : FiveHT2AStateAxis
  receptorContextAxis : FiveHT2AStateAxis
  recognitionGeometryAxis : FiveHT2AStateAxis
  signalingAxis : FiveHT2AStateAxis
  circuitAxis : FiveHT2AStateAxis
  perceptualAxis : FiveHT2AStateAxis

record FiveHT2AStateSpaceBoundary : Set where
  constructor fiveHT2AStateSpaceBoundary
  field
    ligandIdentityAloneFixesState : Bool
    ligandIdentityAloneFixesStateIsFalse :
      ligandIdentityAloneFixesState ≡ false

    receptorContextCanChangeRecognitionStatus : Bool
    receptorContextCanChangeRecognitionStatusIsTrue :
      receptorContextCanChangeRecognitionStatus ≡ true

    recognitionStatusDeterminesSignalingProfile : Bool
    recognitionStatusDeterminesSignalingProfileIsFalse :
      recognitionStatusDeterminesSignalingProfile ≡ false

    signalingProfileDeterminesCircuitState : Bool
    signalingProfileDeterminesCircuitStateIsFalse :
      signalingProfileDeterminesCircuitState ≡ false

    circuitStateDeterminesPercept : Bool
    circuitStateDeterminesPerceptIsFalse :
      circuitStateDeterminesPercept ≡ false

open FiveHT2AStateSpaceBoundary public

canonicalFiveHT2AStateSpaceBoundary :
  FiveHT2AStateSpaceBoundary
canonicalFiveHT2AStateSpaceBoundary =
  fiveHT2AStateSpaceBoundary
    false refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Anti-collapse.
------------------------------------------------------------------------

data MoleculeIdentityIsFullState : Set where
data RecognitionAcceptanceMeansSameSignaling : Set where
data ReceptorContextCanBeIgnored : Set where

moleculeIdentityIsNotFullState :
  MoleculeIdentityIsFullState → ⊥
moleculeIdentityIsNotFullState ()

recognitionAcceptanceDoesNotFixSignaling :
  RecognitionAcceptanceMeansSameSignaling → ⊥
recognitionAcceptanceDoesNotFixSignaling ()

receptorContextCannotBeErased :
  ReceptorContextCanBeIgnored → ⊥
receptorContextCannotBeErased ()
