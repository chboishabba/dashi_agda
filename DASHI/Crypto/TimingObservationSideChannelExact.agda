module DASHI.Crypto.TimingObservationSideChannelExact where

------------------------------------------------------------------------
-- TIMING AS AN OBSERVATION SURFACE
--
-- Paul C. Kocher, "Timing Attacks on Implementations of Diffie-Hellman, RSA,
-- DSS, and Other Systems", CRYPTO 1996, LNCS 1109, 104-113.
-- DOI: 10.1007/3-540-68697-5_9.
--
-- Andres Freund's 2024 xz/liblzma investigation is included as engineering
-- provenance: anomalous CPU/runtime behaviour around sshd helped expose the
-- compromised library path.  No DOI is asserted for the oss-security report.
--
-- Timing is treated exactly like any other observation: if it varies inside a
-- public fibre, it can refine that fibre.  This module does not assert that any
-- named conforming cryptographic implementation has such a split.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Crypto.ChosenCiphertextObservationRefinementExact as Obs

record TimedPublicSystem : Set₁ where
  constructor timedPublicSystem
  field
    Hidden Public Query : Set
    project : Hidden → Public
    runtime : Hidden → Query → Nat

open TimedPublicSystem public

record FibreConstantTiming (system : TimedPublicSystem) : Set₁ where
  constructor fibreConstantTiming
  field
    sameRuntime : ∀ {left right} →
      project system left ≡ project system right →
      ∀ q → runtime system left q ≡ runtime system right q

open FibreConstantTiming public

record TimingSplit (system : TimedPublicSystem) : Set where
  constructor timingSplit
  field
    left right : Hidden system
    samePublic : project system left ≡ project system right
    query : Query system
    runtimeDiffers : runtime system left query ≡ runtime system right query → ⊥

open TimingSplit public

timingSplitRefutesFibreConstant :
  ∀ {system : TimedPublicSystem} →
  TimingSplit system → FibreConstantTiming system → ⊥
timingSplitRefutesFibreConstant split constant =
  runtimeDiffers split
    (sameRuntime constant (samePublic split) (query split))

-- Runtime itself is an observation system.
timingObservationSystem : TimedPublicSystem → Obs.ObservationSystem
timingObservationSystem system =
  Obs.observationSystem (Hidden system) (Query system) Nat (runtime system)

timingSplitGivesObservationSplit :
  ∀ {system : TimedPublicSystem} →
  TimingSplit system → Obs.ObservationSplitWitness (timingObservationSystem system)
timingSplitGivesObservationSplit split =
  Obs.observationSplitWitness
    (left split) (right split) (query split) (runtimeDiffers split)

------------------------------------------------------------------------
-- Coarsened/bucketed timing remains security-relevant whenever the bucket is
-- still able to distinguish two states in the same public fibre.
------------------------------------------------------------------------

record BucketedTimingSplit (system : TimedPublicSystem) : Set₁ where
  constructor bucketedTimingSplit
  field
    Bucket : Set
    bucket : Nat → Bucket
    left right : Hidden system
    samePublic : project system left ≡ project system right
    query : Query system
    bucketDiffers :
      bucket (runtime system left query) ≡
      bucket (runtime system right query) → ⊥

open BucketedTimingSplit public

-- Constant-time at this abstraction means constancy on every public fibre, not
-- merely "usually similar" wall-clock time.
record TimingInvariant (system : TimedPublicSystem) : Set₁ where
  constructor timingInvariant
  field
    publicFibreConstant : FibreConstantTiming system

open TimingInvariant public
