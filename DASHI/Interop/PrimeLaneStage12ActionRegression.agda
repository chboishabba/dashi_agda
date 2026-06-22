module DASHI.Interop.PrimeLaneStage12ActionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.P11PrimeLaneStage12ActionBridge as P11Bridge
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
    registryEnumeratesTwoAdapters :
      Registry.registeredAdapterCount registry ≡ 2

open PrimeLaneStage12ActionRegression public

canonicalPrimeLaneStage12ActionRegression :
  PrimeLaneStage12ActionRegression
canonicalPrimeLaneStage12ActionRegression =
  record
    { p7Adapter = Adapter.canonicalP7PrimeLaneStage12ActionAdapter
    ; p7AdapterIsCanonical = refl
    ; p11Adapter = Adapter.canonicalP11PrimeLaneStage12ActionAdapter
    ; p11AdapterIsCanonical = refl
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
    ; registryEnumeratesTwoAdapters = refl
    }
