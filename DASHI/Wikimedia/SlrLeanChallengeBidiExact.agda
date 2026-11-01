module DASHI.Wikimedia.SlrLeanChallengeBidiExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact as Observation
import DASHI.Wikimedia.LeanWikidataVerificationExact as Verification

------------------------------------------------------------------------
-- SLR -> LEAN CHALLENGE / LEAN -> SLR RESOLUTION ABI
------------------------------------------------------------------------

data ChallengeKind : Set where
  counterexampleCandidate : ChallengeKind
  sameObjectChallenge : ChallengeKind
  freshnessChallenge : ChallengeKind
  typeMismatchChallenge : ChallengeKind
  premiseChallenge : ChallengeKind
  relationAlignmentChallenge : ChallengeKind

data ResolutionKind : Set where
  reproduced : ResolutionKind
  notReproduced : ResolutionKind
  statementTooStrong : ResolutionKind
  statementTooWeak : ResolutionKind
  wrongTypeResolution : ResolutionKind
  wrongObjectResolutionKind : ResolutionKind
  staleImport : ResolutionKind
  encodingDefect : ResolutionKind
  premiseMismatch : ResolutionKind
  unresolvedResolution : ResolutionKind

record SLRLeanChallenge : Set where
  constructor slrLeanChallenge
  field
    challengeReference : String
    challengeKind : ChallengeKind
    targetFormalStatementReference : String
    candidateObjectReference : String
    candidateRelationReference : String
    sourceRevisionReferences : List String
    premiseWitnessReferences : List String
    conflictingObservationReferences : List String
    alignmentReference : String
    candidateOnly : Bool
    challengeIsFormalRefutation : Bool
    challengeCreatesWorldTruth : Bool

open SLRLeanChallenge public

record LeanChallengeResolution : Set where
  constructor leanChallengeResolution
  field
    resolutionReference : String
    challenge : SLRLeanChallenge
    resolutionKind : ResolutionKind
    leanReplayReference : String
    resolutionReasonReference : String
    resolutionCreatesWorldTruth : Bool
    resolutionCreatesLegalAuthority : Bool
    resolutionCreatesAgdaProof : Bool

open LeanChallengeResolution public

data CounterexampleCandidateEqualsFormalRefutation : Set where
data ChallengeReceiptCreatesWorldTruth : Set where
data ChallengeResolutionCreatesLegalAuthority : Set where

data ChallengeResolutionCreatesAgdaProof : Set where

counterexampleCandidateDoesNotEqualFormalRefutation :
  CounterexampleCandidateEqualsFormalRefutation → ⊥
counterexampleCandidateDoesNotEqualFormalRefutation ()

challengeReceiptDoesNotCreateWorldTruth : ChallengeReceiptCreatesWorldTruth → ⊥
challengeReceiptDoesNotCreateWorldTruth ()

challengeResolutionDoesNotCreateLegalAuthority :
  ChallengeResolutionCreatesLegalAuthority → ⊥
challengeResolutionDoesNotCreateLegalAuthority ()

challengeResolutionDoesNotCreateAgdaProof :
  ChallengeResolutionCreatesAgdaProof → ⊥
challengeResolutionDoesNotCreateAgdaProof ()

------------------------------------------------------------------------
-- Imported owners make the intended composition explicit without transferring
-- their authority into this bridge.
------------------------------------------------------------------------

ObservationOwner : Set
ObservationOwner = Observation.WorldObservation

VerificationOwner : Set
VerificationOwner = Verification.LeanVerificationReceipt
