module DASHI.Wikimedia.MaboSlrLeanChallengeReplayFixtureExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.JmdLeanIntegratedMachineLineageExact as Machine
import DASHI.Wikimedia.MaboJmdSlrGetterParityFixtureExact as Parity
open import DASHI.Wikimedia.SlrLeanChallengeBidiExact

------------------------------------------------------------------------
-- CONCRETE MABO SLR -> JMD LEAN CHALLENGE FIXTURE
--
-- The fixture asks the integrated Lean machine to replay freshness/alignment
-- for the already-pinned Mabo P710 relation.  It intentionally carries no
-- LeanChallengeResolution: a source-written challenge is not evidence that the
-- JMD runtime was invoked or that any resolution was observed.
------------------------------------------------------------------------

maboFreshnessChallenge : SLRLeanChallenge
maboFreshnessChallenge =
  slrLeanChallenge
    "challenge:mabo:Q1501525:P710:freshness"
    freshnessChallenge
    "JMD:Wikidata:P710:Q1501525->Q975866"
    "Q1501525"
    "P710"
    ("wikidata:Q1501525:oldid:2333409615" ∷ [])
    ("DASHI.Wikimedia.MaboPropertyTripleProjectionExact.maboParticipantPropertyTriple" ∷ [])
    ("DASHI.Wikimedia.MaboJmdSlrGetterParityFixtureExact.maboGoldenObservation" ∷ [])
    "same-object/relation attachment must be replayed against current source revision"
    true
    false
    false

record MaboChallengeReplayFixture : Set where
  constructor mabo-challenge-replay-fixture
  field
    challengeReceipt : SLRLeanChallenge
    targetMachineRepository : String
    targetMachineCommit : String
    getterParityFixtureReference : String
    targetsCanonicalJmdMachine : Bool
    leanReplayObserved : Bool
    replayResolutionPresent : Bool
    fixtureCreatesWorldTruth : Bool
    fixtureCreatesLegalAuthority : Bool

open MaboChallengeReplayFixture public

canonicalMaboChallengeReplayFixture : MaboChallengeReplayFixture
canonicalMaboChallengeReplayFixture =
  mabo-challenge-replay-fixture
    maboFreshnessChallenge
    Machine.jmdIntegratedRepository
    Machine.jmdIntegratedCommit
    "DASHI.Wikimedia.MaboJmdSlrGetterParityFixtureExact.canonicalMaboGetterParityFixture"
    true
    false
    false
    false
    false

maboChallengeSourceObservation = Parity.maboGoldenObservation

data SourceWrittenChallengeEqualsObservedReplay : Set where
data MissingResolutionEqualsUnresolvedResolution : Set where

data ChallengeTargetCommitEqualsKernelReceipt : Set where

sourceWrittenChallengeDoesNotEqualObservedReplay :
  SourceWrittenChallengeEqualsObservedReplay → ⊥
sourceWrittenChallengeDoesNotEqualObservedReplay ()

missingResolutionDoesNotEqualUnresolvedResolution :
  MissingResolutionEqualsUnresolvedResolution → ⊥
missingResolutionDoesNotEqualUnresolvedResolution ()

challengeTargetCommitDoesNotEqualKernelReceipt :
  ChallengeTargetCommitEqualsKernelReceipt → ⊥
challengeTargetCommitDoesNotEqualKernelReceipt ()
