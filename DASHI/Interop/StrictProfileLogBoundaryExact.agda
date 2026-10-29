{-# OPTIONS --safe #-}
module DASHI.Interop.StrictProfileLogBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

-- Strict is a requested configuration, not runtime attestation.
record StrictLogProfile : Set where
  constructor strictLogProfile
  field
    profileName : String
    version : Nat
    strictRequested : Bool

record LogEntry : Set where
  constructor logEntry
  field
    profile : StrictLogProfile
    message : String
    runtimeVerified : Bool

appendStrictLog : String → Nat → String → LogEntry
appendStrictLog name version message =
  logEntry (strictLogProfile name version true) message false

appendRequestsStrict : (name : String) (version : Nat) (message : String) →
  StrictLogProfile.strictRequested
    (LogEntry.profile (appendStrictLog name version message)) ≡ true
appendRequestsStrict name version message = refl

appendPreservesVersion : (name : String) (version : Nat) (message : String) →
  StrictLogProfile.version
    (LogEntry.profile (appendStrictLog name version message)) ≡ version
appendPreservesVersion name version message = refl

appendDoesNotAttestRuntime : (name : String) (version : Nat) (message : String) →
  LogEntry.runtimeVerified (appendStrictLog name version message) ≡ false
appendDoesNotAttestRuntime name version message = refl
