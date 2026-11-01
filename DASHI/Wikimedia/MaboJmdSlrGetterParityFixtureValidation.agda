module DASHI.Wikimedia.MaboJmdSlrGetterParityFixtureValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact
open import DASHI.Wikimedia.MaboJmdSlrGetterParityFixtureExact

_ : objectReference maboGoldenObservation ≡ "Q1501525"
_ = refl

_ : relationReference maboGoldenObservation ≡ "P710"
_ = refl

_ : observedValueReference maboGoldenObservation ≡ "Q975866"
_ = refl

_ : sourceRevisionReference maboGoldenObservation ≡ "wikidata:Q1501525:oldid:2333409615"
_ = refl

_ : normalizeLeanGetter maboLeanGetterFixture ≡ maboGoldenObservation
_ = refl

_ : normalizeSlrGetter maboSlrGetterFixture ≡ maboGoldenObservation
_ = refl

_ : fixtureUsesExactMaboPropertyTriple canonicalMaboGetterParityFixture ≡ true
_ = refl

_ : runtimeParityObserved canonicalMaboGetterParityFixture ≡ false
_ = refl

_ : fixtureCreatesWorldTruth canonicalMaboGetterParityFixture ≡ false
_ = refl
