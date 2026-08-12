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
-- compromised library path. No DOI is asserted for the oss-security report.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

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
  runtimeDiffers split (sameRuntime constant (samePublic split) (query split))

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
-- Timing can reveal much less than the hidden state and still reveal the
-- desired/protected result. This is the timing analogue of public secret-label
-- factorisation: a decoder maps elapsed-time observation to a protected outcome.
------------------------------------------------------------------------

record TimingOutcomeFactorisation (system : TimedPublicSystem) : Set₁ where
  constructor timingOutcomeFactorisation
  field
    Outcome : Set
    protectedOutcome : Hidden system → Outcome
    chosenQuery : Query system
    decodeRuntime : Nat → Outcome
    outcomeFactorsThroughTiming : ∀ hidden →
      decodeRuntime (runtime system hidden chosenQuery) ≡ protectedOutcome hidden
open TimingOutcomeFactorisation public

TimingRevealsOutcome :
  ∀ {system : TimedPublicSystem} →
  TimingOutcomeFactorisation system → Set
TimingRevealsOutcome {system} factorisation =
  ∀ hidden →
    decodeRuntime factorisation
      (runtime system hidden (chosenQuery factorisation)) ≡
    protectedOutcome factorisation hidden

timingFactorisationRevealsOutcome :
  ∀ {system : TimedPublicSystem}
    (factorisation : TimingOutcomeFactorisation system) →
  TimingRevealsOutcome factorisation
timingFactorisationRevealsOutcome factorisation =
  outcomeFactorsThroughTiming factorisation

------------------------------------------------------------------------
-- Coarsened/bucketed timing can still split a fibre.
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

record TimingInvariant (system : TimedPublicSystem) : Set₁ where
  constructor timingInvariant
  field publicFibreConstant : FibreConstantTiming system
open TimingInvariant public
