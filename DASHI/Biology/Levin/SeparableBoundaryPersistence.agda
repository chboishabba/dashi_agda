module DASHI.Biology.Levin.SeparableBoundaryPersistence where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record InteractionBoundary : Set where
  field
    internalDimension : Nat
    boundaryDimension : Nat
    environmentDimension : Nat
    sparseRelativeToInterior : Bool

record PersistenceWitness : Set where
  field
    boundary : InteractionBoundary
    boundaryRemainsClosed : Bool
    exchangeRemainsBounded : Bool
    systemRemainsDistinguishable : Bool

record BoundaryPersistenceBoundary : Set where
  field
    separabilityRequiresWitness : Bool
    markovBlanketIsNotDefinitionallyAnyBoundary : Bool
    persistenceDoesNotImplyConsciousness : Bool
    persistenceDoesNotImplyBiologicalLife : Bool
    interpretation : String

canonicalBoundaryPersistenceBoundary : BoundaryPersistenceBoundary
canonicalBoundaryPersistenceBoundary = record
  { separabilityRequiresWitness = true
  ; markovBlanketIsNotDefinitionallyAnyBoundary = true
  ; persistenceDoesNotImplyConsciousness = true
  ; persistenceDoesNotImplyBiologicalLife = true
  ; interpretation = "Persistent distinguishability is represented through a bounded sparse interaction boundary; intelligence and life remain separate interpretive predicates"
  }
