module DASHI.Law.QueryWorldFormalWitnessStalenessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- S15 × S18: formal witnesses are projection-coordinate scoped.
--
-- A checked FactorsThrough / QueryAdequacyDefect witness is usable only for
-- the exact query projection digest it certifies.  When W₀ → W₁ changes that
-- digest, the old witness becomes stale evidence; this is not a contradiction
-- and not a runtime failure.
------------------------------------------------------------------------

data ProjectionDigest : Set where
  d₀ d₁ : ProjectionDigest

d₀≠d₁ : d₀ ≡ d₁ → ⊥
d₀≠d₁ ()

record CheckedFactorsThroughWitness : Set where
  constructor checkedFactorsThroughWitness
  field
    positiveCertifiedDigest : ProjectionDigest

record CheckedNonFactorabilityWitness : Set where
  constructor checkedNonFactorabilityWitness
  field
    certifiedDigest : ProjectionDigest

open CheckedFactorsThroughWitness public
open CheckedNonFactorabilityWitness public

data PositiveWitnessUsableAt
    (witness : CheckedFactorsThroughWitness)
    (current : ProjectionDigest) : Set where
  exactPositiveDigest :
    positiveCertifiedDigest witness ≡ current →
    PositiveWitnessUsableAt witness current

data NegativeWitnessUsableAt
    (witness : CheckedNonFactorabilityWitness)
    (current : ProjectionDigest) : Set where
  exactNegativeDigest :
    negativeCertifiedDigest witness ≡ current →
    NegativeWitnessUsableAt witness current

oldPositive : CheckedFactorsThroughWitness
oldPositive = checkedFactorsThroughWitness d₀

oldNegative : CheckedNonFactorabilityWitness
oldNegative = checkedNonFactorabilityWitness d₀

oldPositiveCannotCertifyNewProjection :
  PositiveWitnessUsableAt oldPositive d₁ → ⊥
oldPositiveCannotCertifyNewProjection (exactPositiveDigest digestEq) =
  d₀≠d₁ digestEq

oldNegativeCannotReopenNewProjection :
  NegativeWitnessUsableAt oldNegative d₁ → ⊥
oldNegativeCannotReopenNewProjection (exactNegativeDigest digestEq) =
  d₀≠d₁ digestEq

oldPositiveRemainsUsableAtOriginalProjection :
  PositiveWitnessUsableAt oldPositive d₀
oldPositiveRemainsUsableAtOriginalProjection =
  exactPositiveDigest refl

oldNegativeRemainsUsableAtOriginalProjection :
  NegativeWitnessUsableAt oldNegative d₀
oldNegativeRemainsUsableAtOriginalProjection =
  exactNegativeDigest refl

record QueryWorldFormalWitnessStalenessBoundary : Set where
  constructor queryWorldFormalWitnessStalenessBoundary
  field
    factorsThroughWitnessRequiresExactProjectionDigest : Bool
    factorsThroughWitnessRequiresExactProjectionDigestIsTrue :
      factorsThroughWitnessRequiresExactProjectionDigest ≡ true

    nonfactorabilityWitnessRequiresExactProjectionDigest : Bool
    nonfactorabilityWitnessRequiresExactProjectionDigestIsTrue :
      nonfactorabilityWitnessRequiresExactProjectionDigest ≡ true

    changedProjectionMayMakeOldPositiveWitnessStale : Bool
    changedProjectionMayMakeOldPositiveWitnessStaleIsTrue :
      changedProjectionMayMakeOldPositiveWitnessStale ≡ true

    changedProjectionMayMakeOldNegativeWitnessStale : Bool
    changedProjectionMayMakeOldNegativeWitnessStaleIsTrue :
      changedProjectionMayMakeOldNegativeWitnessStale ≡ true

    staleWitnessIsRuntimeContradiction : Bool
    staleWitnessIsRuntimeContradictionIsFalse :
      staleWitnessIsRuntimeContradiction ≡ false

    staleWitnessCreatesSemanticAuthority : Bool
    staleWitnessCreatesSemanticAuthorityIsFalse :
      staleWitnessCreatesSemanticAuthority ≡ false

    staleWitnessCreatesClaimTruth : Bool
    staleWitnessCreatesClaimTruthIsFalse :
      staleWitnessCreatesClaimTruth ≡ false

open QueryWorldFormalWitnessStalenessBoundary public

canonicalQueryWorldFormalWitnessStalenessBoundary :
  QueryWorldFormalWitnessStalenessBoundary
canonicalQueryWorldFormalWitnessStalenessBoundary =
  queryWorldFormalWitnessStalenessBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl