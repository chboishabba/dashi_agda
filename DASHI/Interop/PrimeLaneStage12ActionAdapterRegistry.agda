module DASHI.Interop.PrimeLaneStage12ActionAdapterRegistry where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Interop.PrimeLaneStage12ActionAdapter as Adapter

------------------------------------------------------------------------
-- Canonical prime-lane Stage12 adapter registry.
--
-- The Stage12 adapter layer now has three concrete canonical rows, p7, p11,
-- and the full p13 closure witness.
-- This registry enumerates those rows without inventing any extra authority.

data PrimeLaneStage12ActionAdapterRegistryBoundary : Set where
  referenceOnly : PrimeLaneStage12ActionAdapterRegistryBoundary
  noPhysicsClaim : PrimeLaneStage12ActionAdapterRegistryBoundary

data PrimeLaneStage12ActionAdapterRegistryEntry : Set where
  canonicalAdapterEntry :
    String →
    Adapter.PrimeLaneStage12ActionAdapter →
    PrimeLaneStage12ActionAdapterRegistryEntry
  reservedAdapterEntry :
    String →
    List String →
    PrimeLaneStage12ActionAdapterRegistryEntry

record PrimeLaneStage12ActionAdapterRegistry : Set₁ where
  field
    registryLabel :
      String
    registryBoundary :
      PrimeLaneStage12ActionAdapterRegistryBoundary
    registryEntries :
      List PrimeLaneStage12ActionAdapterRegistryEntry
    registeredAdapterCount :
      Nat
    canonicalAdapterCount :
      Nat
    enumeratesP7 :
      Bool
    enumeratesP7IsTrue :
      enumeratesP7 ≡ true
    enumeratesP11 :
      Bool
    enumeratesP11IsTrue :
      enumeratesP11 ≡ true
    enumeratesP13 :
      Bool
    enumeratesP13IsTrue :
      enumeratesP13 ≡ true
    notes :
      List String

open PrimeLaneStage12ActionAdapterRegistry public
open PrimeLaneStage12ActionAdapterRegistryEntry public

canonicalPrimeLaneStage12ActionAdapterEntries :
  List PrimeLaneStage12ActionAdapterRegistryEntry
canonicalPrimeLaneStage12ActionAdapterEntries =
  canonicalAdapterEntry
    "p7"
    Adapter.canonicalP7PrimeLaneStage12ActionAdapter
  ∷ canonicalAdapterEntry
    "p11"
    Adapter.canonicalP11PrimeLaneStage12ActionAdapter
  ∷ canonicalAdapterEntry
    "p13"
    Adapter.canonicalP13PrimeLaneStage12ActionAdapter
  ∷ []

canonicalPrimeLaneStage12ActionAdapterRegistry :
  PrimeLaneStage12ActionAdapterRegistry
canonicalPrimeLaneStage12ActionAdapterRegistry =
  record
    { registryLabel =
        "canonical-prime-lane-stage12-action-adapter-registry"
    ; registryBoundary =
        referenceOnly
    ; registryEntries =
        canonicalPrimeLaneStage12ActionAdapterEntries
    ; registeredAdapterCount =
        3
    ; canonicalAdapterCount =
        3
    ; enumeratesP7 =
        true
    ; enumeratesP7IsTrue =
        refl
    ; enumeratesP11 =
        true
    ; enumeratesP11IsTrue =
        refl
    ; enumeratesP13 =
        true
    ; enumeratesP13IsTrue =
        refl
    ; notes =
        "p7, p11, and the p13 full Stage12 witness now consume the same Stage12 prime-lane adapter contract and are enumerated here."
      ∷ "The registry is intentionally narrow: it enumerates canonical prime-lane Stage12 adapters only."
      ∷ "Future prime lanes should join this registry by consuming the same shared Stage12 adapter contract."
      ∷ []
    }
