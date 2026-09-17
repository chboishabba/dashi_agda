module DASHI.Wikimedia.MaboSlrLeanChallengeReplayFixtureValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Wikimedia.SlrLeanChallengeBidiExact
open import DASHI.Wikimedia.MaboSlrLeanChallengeReplayFixtureExact

_ : challengeKind maboFreshnessChallenge ≡ freshnessChallenge
_ = refl

_ : candidateOnly maboFreshnessChallenge ≡ true
_ = refl

_ : challengeIsFormalRefutation maboFreshnessChallenge ≡ false
_ = refl

_ : targetsCanonicalJmdMachine canonicalMaboChallengeReplayFixture ≡ true
_ = refl

_ : leanReplayObserved canonicalMaboChallengeReplayFixture ≡ false
_ = refl

_ : replayResolutionPresent canonicalMaboChallengeReplayFixture ≡ false
_ = refl

_ : fixtureCreatesWorldTruth canonicalMaboChallengeReplayFixture ≡ false
_ = refl
