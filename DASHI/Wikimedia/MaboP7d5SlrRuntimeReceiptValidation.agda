module DASHI.Wikimedia.MaboP7d5SlrRuntimeReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Wikimedia.MaboP7d5SlrRuntimeReceiptExact

_ : slrP7d5Head ≡ "efba015c78480c324c4f99d7ec8dab4a31020640"
_ = refl

_ : cargoWorkspaceGreen slrP7d5Execution ≡ true
_ = refl

_ : clippyWorkspaceGreen slrP7d5Execution ≡ true
_ = refl

_ : liveProviderSmokeObserved slrP7d5Execution ≡ true
_ = refl

_ : p710ObjectRef liveMaboP710Observation ≡ "Q1501525"
_ = refl

_ : p710RelationRef liveMaboP710Observation ≡ "P710"
_ = refl

_ : p710ValueRef liveMaboP710Observation ≡ "Q975866"
_ = refl

_ : p710RevisionRef liveMaboP710Observation ≡
    "wikidata:Q1501525:oldid:2333409615"
_ = refl

_ : p710ContentDigestRef liveMaboP710Observation ≡
    "sha256:43681681a832e9d0edf09f745c7d3e71fd4cdb9fd23d4670f25e5b94827b5eba"
_ = refl

_ : p710DirectPropertyCandidates liveMaboP710Observation ≡ 14
_ = refl

_ : p710CandidateOnly liveMaboP710Observation ≡ true
_ = refl

_ : p710CreatesSemanticAuthority liveMaboP710Observation ≡ false
_ = refl

_ : p710ClaimTruthPromoted liveMaboP710Observation ≡ false
_ = refl

_ : identityClassRef liveMaboCaseLineage ≡ "world-object:mabo-case-1992-hca-23"
_ = refl

_ : identityClassRef liveEddieMaboLineage ≡ "world-object:eddie-mabo"
_ = refl

_ : lineageCandidateOnly liveMaboCaseLineage ≡ true
_ = refl

_ : lineageCandidateOnly liveEddieMaboLineage ≡ true
_ = refl

_ : lineageCreatesSemanticAuthority liveMaboCaseLineage ≡ false
_ = refl

_ : lineageClaimTruthPromoted liveEddieMaboLineage ≡ false
_ = refl

_ : getterParityBridgeCargoCertified slrP7d5Payment ≡ true
_ = refl

_ : crossBackendParityObserved slrP7d5Payment ≡ false
_ = refl

_ : jmdGetterRuntimeObserved slrP7d5Payment ≡ false
_ = refl

_ : jmdChallengeReplayObserved slrP7d5Payment ≡ false
_ = refl
