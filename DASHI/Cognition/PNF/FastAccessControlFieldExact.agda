module DASHI.Cognition.PNF.FastAccessControlFieldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Generic fast-access layer.
--
-- This is deliberately NOT a neural-wave theory.  It is the consumer-facing
-- operator required by PNF/memory: a fine carrier may remain literally fixed
-- while a time/context-indexed access map changes whether that carrier is
-- effectively recruitable.  Physical wave dynamics are one possible producer.
------------------------------------------------------------------------

record FastAccessControlField : Set₁ where
  field
    Carrier : Set
    Time : Set
    Context : Set
    accessAt : Time → Context → Carrier → Bool

open FastAccessControlField public

record RetentionWithoutAccessWitness
  (F : FastAccessControlField) : Set where
  constructor retentionWithoutAccessWitness
  field
    retained : Carrier F
    firstTime secondTime : Time F
    context : Context F
    firstAccess secondAccess : Bool
    firstAccess-v : accessAt F firstTime context retained ≡ firstAccess
    secondAccess-v : accessAt F secondTime context retained ≡ secondAccess
    accessChanged : firstAccess ≡ secondAccess → ⊥

open RetentionWithoutAccessWitness public

record ContextAccessContrast
  (F : FastAccessControlField) : Set where
  constructor contextAccessContrast
  field
    retained : Carrier F
    time : Time F
    firstContext secondContext : Context F
    firstAccess secondAccess : Bool
    firstAccess-v : accessAt F time firstContext retained ≡ firstAccess
    secondAccess-v : accessAt F time secondContext retained ≡ secondAccess
    accessChanged : firstAccess ≡ secondAccess → ⊥

open ContextAccessContrast public

data Tick2 : Set where firstTick secondTick : Tick2
data Context2 : Set where restrictiveContext permissiveContext : Context2

data Carrier2 : Set where retainedA retainedB : Carrier2

canonicalAccess : Tick2 → Context2 → Carrier2 → Bool
canonicalAccess firstTick restrictiveContext _ = false
canonicalAccess secondTick restrictiveContext retainedA = true
canonicalAccess secondTick restrictiveContext retainedB = false
canonicalAccess firstTick permissiveContext _ = true
canonicalAccess secondTick permissiveContext _ = true

canonicalFastAccessControlField : FastAccessControlField
canonicalFastAccessControlField = record
  { Carrier = Carrier2
  ; Time = Tick2
  ; Context = Context2
  ; accessAt = canonicalAccess
  }

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

canonicalRetentionWithoutAccess :
  RetentionWithoutAccessWitness canonicalFastAccessControlField
canonicalRetentionWithoutAccess =
  retentionWithoutAccessWitness
    retainedA firstTick secondTick restrictiveContext
    false true refl refl falseNotTrue

canonicalContextChangesAccess :
  ContextAccessContrast canonicalFastAccessControlField
canonicalContextChangesAccess =
  contextAccessContrast
    retainedB firstTick restrictiveContext permissiveContext
    false true refl refl falseNotTrue

------------------------------------------------------------------------
-- Boundary: this layer changes effective accessibility only.  It contains no
-- semantic revision constructor, no truth promotion, and no typed-meet result.
------------------------------------------------------------------------

record FastAccessControlBoundary : Set where
  constructor fastAccessControlBoundary
  field
    accessChangeIsSemanticRevision : Bool
    accessFailureIsNoTypedMeet : Bool
    accessSuccessIsTruth : Bool
    physicalWaveProducerRequiredByDefinition : Bool

canonicalFastAccessControlBoundary : FastAccessControlBoundary
canonicalFastAccessControlBoundary =
  fastAccessControlBoundary false false false false
