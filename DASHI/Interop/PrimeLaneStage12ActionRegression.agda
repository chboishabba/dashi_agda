module DASHI.Interop.PrimeLaneStage12ActionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.P11PrimeLaneStage12ActionBridge as P11Bridge
import DASHI.Interop.P13PrimeLaneStage12ActionBridge as P13Bridge
import DASHI.Interop.P7PrimeLaneStage12ActionBridge as P7Bridge
import DASHI.Interop.PrimeLaneStage12ActionAdapter as Adapter
import DASHI.Interop.PrimeLaneStage12ActionAdapterRegistry as Registry
import DASHI.Interop.PrimeLaneStage12ActionCarryBridge as CarryBridge
import DASHI.Interop.PrimeLaneStage12ActionSuccessorBridge as SuccessorBridge

record PrimeLaneStage12ActionRegression : Set₁ where
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
    registry :
      Registry.PrimeLaneStage12ActionAdapterRegistry
    registryIsCanonical :
      registry ≡ Registry.canonicalPrimeLaneStage12ActionAdapterRegistry
    carryBridge :
      CarryBridge.PrimeLaneStage12ActionCarryBridge
    carryBridgeIsCanonical :
      carryBridge ≡ CarryBridge.canonicalPrimeLaneStage12ActionCarryBridge
    successorBridge :
      SuccessorBridge.PrimeLaneStage12ActionSuccessorBridge
    successorBridgeIsCanonical :
      successorBridge ≡ SuccessorBridge.canonicalPrimeLaneStage12ActionSuccessorBridge
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
    registryEnumeratesThreeAdapters :
      Registry.registeredAdapterCount registry ≡ 3

open PrimeLaneStage12ActionRegression public

canonicalPrimeLaneStage12ActionRegression :
  PrimeLaneStage12ActionRegression
canonicalPrimeLaneStage12ActionRegression =
  record
    { p7Adapter = Adapter.canonicalP7PrimeLaneStage12ActionAdapter
    ; p7AdapterIsCanonical = refl
    ; p11Adapter = Adapter.canonicalP11PrimeLaneStage12ActionAdapter
    ; p11AdapterIsCanonical = refl
    ; p13Adapter = Adapter.canonicalP13PrimeLaneStage12ActionAdapter
    ; p13AdapterIsCanonical = refl
    ; registry = Registry.canonicalPrimeLaneStage12ActionAdapterRegistry
    ; registryIsCanonical = refl
    ; carryBridge = CarryBridge.canonicalPrimeLaneStage12ActionCarryBridge
    ; carryBridgeIsCanonical = refl
    ; successorBridge =
        SuccessorBridge.canonicalPrimeLaneStage12ActionSuccessorBridge
    ; successorBridgeIsCanonical = refl
    ; p7Bridge = P7Bridge.canonicalP7PrimeLaneStage12ActionBridge
    ; p7BridgeIsCanonical = refl
    ; p11Bridge = P11Bridge.canonicalP11PrimeLaneStage12ActionBridge
    ; p11BridgeIsCanonical = refl
    ; p13Bridge = P13Bridge.canonicalP13PrimeLaneStage12ActionBridge
    ; p13BridgeIsCanonical = refl
    ; registryEnumeratesThreeAdapters = refl
    }
