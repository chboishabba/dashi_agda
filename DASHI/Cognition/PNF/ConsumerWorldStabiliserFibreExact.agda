module DASHI.Cognition.PNF.ConsumerWorldStabiliserFibreExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.BracketedTSFVFractranWorldFibreExact as World
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- Query-relative observational equivalence.  We deliberately do not promote a
-- global symmetry group: admissible transformations are typed, partial and may
-- change when the bracket, stratum, query or history changes.
------------------------------------------------------------------------

record WorldObservation : Set where
  constructor worldObservation
  field
    world : World.WorldHistory
    prime : Signed.SSPPrime
    visible : Trit.SSPTrit

open WorldObservation public

record ConsumerEquivalentWorlds : Set where
  constructor consumerEquivalentWorlds
  field
    left right : WorldObservation
    samePrime : prime left ≡ prime right
    sameVisible : visible left ≡ visible right

open ConsumerEquivalentWorlds public

record ResidualWorldOrbit : Set where
  constructor residualWorldOrbit
  field
    representative : WorldObservation
    alternatives : Context.ResidualWorldFibre

open ResidualWorldOrbit public

record SituatedWorldTransport : Set where
  constructor situatedWorldTransport
  field
    source target : World.WorldHistory
    preservesCurrentConsumer : Bool
    bracketAdmissible : Bool
    stratumAdmissible : Bool
    historyAdmissible : Bool

open SituatedWorldTransport public

isConsumerStabilising : SituatedWorldTransport → Bool
isConsumerStabilising
  (situatedWorldTransport source target true true true true) = true
isConsumerStabilising _ = false

record ConsumerStabiliserBoundary : Set where
  constructor consumerStabiliserBoundary
  field
    observationalEquivalenceMeansWorldIdentity : Bool
    allConsumerStabilisersFormOneGlobalGroupHere : Bool
    stabiliserMayChangeWhenQueryOrBracketChanges : Bool
    residualWorldOrbitRetainsFineAlternatives : Bool

canonicalConsumerStabiliserBoundary : ConsumerStabiliserBoundary
canonicalConsumerStabiliserBoundary =
  consumerStabiliserBoundary false false true true
