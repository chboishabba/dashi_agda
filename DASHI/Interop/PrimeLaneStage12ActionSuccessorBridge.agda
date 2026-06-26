module DASHI.Interop.PrimeLaneStage12ActionSuccessorBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Interop.P11PrimeLaneStage12ActionBridge as P11Bridge
import DASHI.Interop.P13PrimeLaneStage12ActionBridge as P13Bridge
import DASHI.Interop.P7PrimeLaneStage12ActionBridge as P7Bridge
import DASHI.Interop.PrimeLaneStage12ActionAdapter as Adapter
import DASHI.Interop.PrimeSuccessorWitness as Successor

record PrimeLaneStage12ActionSuccessorBridgeAuthorityBits : Set where
  field
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    promotedStageSpine : Bool
    promotedStageSpineIsFalse : promotedStageSpine ≡ false
    promotedPrimeUniversal : Bool
    promotedPrimeUniversalIsFalse : promotedPrimeUniversal ≡ false

canonicalPrimeLaneStage12ActionSuccessorBridgeAuthorityBits :
  PrimeLaneStage12ActionSuccessorBridgeAuthorityBits
canonicalPrimeLaneStage12ActionSuccessorBridgeAuthorityBits =
  record
    { candidateOnly = true
    ; candidateOnlyIsTrue = refl
    ; promotedStageSpine = false
    ; promotedStageSpineIsFalse = refl
    ; promotedPrimeUniversal = false
    ; promotedPrimeUniversalIsFalse = refl
    }

record PrimeLaneStage12ActionSuccessorBridge : Set where
  field
    p7Adapter :
      Adapter.PrimeLaneStage12ActionAdapter
    p7AdapterIsCanonical :
      p7Adapter ≡ Adapter.canonicalP7PrimeLaneStage12ActionAdapter
    p11Adapter :
      Adapter.PrimeLaneStage12ActionAdapter
    p11AdapterIsCanonical :
      p11Adapter ≡ Adapter.canonicalP11PrimeLaneStage12ActionAdapter
    p13Adapter :
      Adapter.PrimeLaneStage12ActionAdapter
    p13AdapterIsCanonical :
      p13Adapter ≡ Adapter.canonicalP13PrimeLaneStage12ActionAdapter
    p7SuccessorWitness :
      Successor.PrimeSuccessorWitness
    p7SuccessorWitnessIsCanonical :
      p7SuccessorWitness ≡ Successor.canonicalP7PrimeSuccessorWitness
    p11SuccessorWitness :
      Successor.PrimeSuccessorWitness
    p11SuccessorWitnessIsCanonical :
      p11SuccessorWitness ≡ Successor.canonicalP11PrimeSuccessorWitness
    p13SuccessorWitness :
      Successor.PrimeSuccessorWitness
    p13SuccessorWitnessIsCanonical :
      p13SuccessorWitness ≡ Successor.canonicalP13PrimeSuccessorWitness
    p7StageWindowWitness :
      Successor.StageSuccessorWitness
    p7StageWindowWitnessIsCanonical :
      p7StageWindowWitness ≡ Successor.canonicalStage6SuccessorWitness
    p11StageWindowWitness :
      Successor.StageSuccessorWitness
    p11StageWindowWitnessIsCanonical :
      p11StageWindowWitness ≡ Successor.canonicalStage10SuccessorWitness
    p13StageWindowWitness :
      Successor.StageSuccessorWitness
    p13StageWindowWitnessIsCanonical :
      p13StageWindowWitness ≡ Successor.canonicalStage12SuccessorWitness
    adapterListMatchesCanonical :
      Adapter.canonicalPrimeLaneStage12ActionAdapters
      ≡
      p7Adapter ∷ p11Adapter ∷ p13Adapter ∷ []
    p7Bridge :
      P7Bridge.P7PrimeLaneStage12ActionBridge
    p7BridgeIsCanonical :
      p7Bridge ≡ P7Bridge.canonicalP7PrimeLaneStage12ActionBridge
    p11Bridge :
      P11Bridge.P11PrimeLaneStage12ActionBridge
    p11BridgeIsCanonical :
      p11Bridge ≡ P11Bridge.canonicalP11PrimeLaneStage12ActionBridge
    p13Bridge :
      P13Bridge.P13PrimeLaneStage12ActionBridge
    p13BridgeIsCanonical :
      p13Bridge ≡ P13Bridge.canonicalP13PrimeLaneStage12ActionBridge
    notes :
      List String
    authorityBits :
      PrimeLaneStage12ActionSuccessorBridgeAuthorityBits

open PrimeLaneStage12ActionSuccessorBridge public

canonicalPrimeLaneStage12ActionSuccessorBridge :
  PrimeLaneStage12ActionSuccessorBridge
canonicalPrimeLaneStage12ActionSuccessorBridge =
  record
    { p7Adapter = Adapter.canonicalP7PrimeLaneStage12ActionAdapter
    ; p7AdapterIsCanonical = refl
    ; p11Adapter = Adapter.canonicalP11PrimeLaneStage12ActionAdapter
    ; p11AdapterIsCanonical = refl
    ; p13Adapter = Adapter.canonicalP13PrimeLaneStage12ActionAdapter
    ; p13AdapterIsCanonical = refl
    ; p7SuccessorWitness = Successor.canonicalP7PrimeSuccessorWitness
    ; p7SuccessorWitnessIsCanonical = refl
    ; p11SuccessorWitness = Successor.canonicalP11PrimeSuccessorWitness
    ; p11SuccessorWitnessIsCanonical = refl
    ; p13SuccessorWitness = Successor.canonicalP13PrimeSuccessorWitness
    ; p13SuccessorWitnessIsCanonical = refl
    ; p7StageWindowWitness = Successor.canonicalStage6SuccessorWitness
    ; p7StageWindowWitnessIsCanonical = refl
    ; p11StageWindowWitness = Successor.canonicalStage10SuccessorWitness
    ; p11StageWindowWitnessIsCanonical = refl
    ; p13StageWindowWitness = Successor.canonicalStage12SuccessorWitness
    ; p13StageWindowWitnessIsCanonical = refl
    ; adapterListMatchesCanonical = refl
    ; p7Bridge = P7Bridge.canonicalP7PrimeLaneStage12ActionBridge
    ; p7BridgeIsCanonical = refl
    ; p11Bridge = P11Bridge.canonicalP11PrimeLaneStage12ActionBridge
    ; p11BridgeIsCanonical = refl
    ; p13Bridge = P13Bridge.canonicalP13PrimeLaneStage12ActionBridge
    ; p13BridgeIsCanonical = refl
    ; notes =
        "The Stage12 successor bridge now carries the canonical p7, p11, and p13 prime-lane adapters."
      ∷ "p7, p11, and the p13 closure witness consume the same adapter contract while keeping their own successor witnesses and local regressions."
      ∷ []
    ; authorityBits = canonicalPrimeLaneStage12ActionSuccessorBridgeAuthorityBits
    }
