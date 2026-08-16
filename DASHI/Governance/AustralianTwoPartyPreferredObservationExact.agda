module DASHI.Governance.AustralianTwoPartyPreferredObservationExact where

------------------------------------------------------------------------
-- AUSTRALIAN TWO-PARTY-PREFERRED AS OBSERVATION COMPRESSION
--
-- Primary sources:
-- Australian Electoral Commission (AEC),
-- "Counting the votes - Frequently Asked Questions" and
-- "How the House of Representatives result is determined".
-- Institution/author: Australian Electoral Commission.
-- Venue: official AEC electoral-administration guidance.
-- DOI: no DOI asserted.
--
-- The AEC defines two-party-preferred (TPP) as the distribution of preferences
-- between the Australian Labor Party and the Liberal/National Coalition.  In a
-- division where those are not the final two candidates, a further scrutiny for
-- information can produce a notional TPP result.
--
-- Source role: TPP is therefore a legitimate bounded two-bloc observation for
-- a declared electoral/statistical query.  It is not evidence that the full
-- political state contains only two parties, candidates, ideologies or voter
-- preference histories.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record ElectoralSourceReceipt : Set where
  constructor electoralSourceReceipt
  field
    institutionAuthor : String
    title : String
    venue : String
    yearOrAccessScope : String
    doi : String
    boundedRole : String

open ElectoralSourceReceipt public

aecCountingReceipt : ElectoralSourceReceipt
aecCountingReceipt = electoralSourceReceipt
  "Australian Electoral Commission"
  "Counting the votes - Frequently Asked Questions"
  "official AEC electoral-administration guidance"
  "current official guidance; bounded to the cited TPP/TCP definitions"
  "no DOI asserted"
  "defines TPP as preference distribution between Labor and Coalition; does not assert political reality is intrinsically binary"

aecHouseCountReceipt : ElectoralSourceReceipt
aecHouseCountReceipt = electoralSourceReceipt
  "Australian Electoral Commission"
  "How the House of Representatives result is determined"
  "official AEC electoral-administration guidance"
  "current official guidance; bounded to House preference distribution and notional TPP scrutiny"
  "no DOI asserted"
  "documents notional TPP scrutiny where Labor and Coalition are not the actual final two candidates"

------------------------------------------------------------------------
-- Finite observation witness.
------------------------------------------------------------------------

data FirstPreference : Set where
  laborFirst coalitionFirst greensFirst independentFirst otherFirst : FirstPreference

data MajorBloc : Set where
  laborBloc coalitionBloc : MajorBloc

data PreferenceHistory : Set where
  greensToLabor independentToLabor laborDirect coalitionDirect otherToCoalition : PreferenceHistory

firstPreference : PreferenceHistory → FirstPreference
firstPreference greensToLabor = greensFirst
firstPreference independentToLabor = independentFirst
firstPreference laborDirect = laborFirst
firstPreference coalitionDirect = coalitionFirst
firstPreference otherToCoalition = otherFirst

tppObservation : PreferenceHistory → MajorBloc
tppObservation greensToLabor = laborBloc
tppObservation independentToLabor = laborBloc
tppObservation laborDirect = laborBloc
tppObservation coalitionDirect = coalitionBloc
tppObservation otherToCoalition = coalitionBloc

------------------------------------------------------------------------
-- Two different first-preference histories can have the same TPP observation.
------------------------------------------------------------------------

greensAndIndependentCollapseInTPP :
  tppObservation greensToLabor ≡ tppObservation independentToLabor
greensAndIndependentCollapseInTPP = refl

greensAndIndependentFirstPreferencesDiffer :
  firstPreference greensToLabor ≡ firstPreference independentToLabor → ⊥
greensAndIndependentFirstPreferencesDiffer ()

TPPInjective : Set
TPPInjective =
  (x y : PreferenceHistory) →
  tppObservation x ≡ tppObservation y →
  x ≡ y

tppObservationIsNotInjective : TPPInjective → ⊥
tppObservationIsNotInjective injective =
  impossible (injective greensToLabor independentToLabor refl)
  where
    impossible : greensToLabor ≡ independentToLabor → ⊥
    impossible ()

------------------------------------------------------------------------
-- Semantic boundary: a useful two-bloc statistic is not a two-state ontology.
------------------------------------------------------------------------

data TPPPromotesLiteralPoliticalDuopoly : Set where

data TPPPromotesTwoIdeologyOntology : Set where

data TPPPromotesCoercion : Set where

notionalTPPDoesNotPromoteLiteralDuopoly :
  TPPPromotesLiteralPoliticalDuopoly → ⊥
notionalTPPDoesNotPromoteLiteralDuopoly ()

tppDoesNotPromoteTwoIdeologyOntology : TPPPromotesTwoIdeologyOntology → ⊥
tppDoesNotPromoteTwoIdeologyOntology ()

tppDoesNotPromoteCoercion : TPPPromotesCoercion → ⊥
tppDoesNotPromoteCoercion ()

record AustralianTPPObservationBoundary : Set where
  constructor australianTPPObservationBoundary
  field
    tppIsDeclaredTwoBlocObservation : Bool
    tppCanBeNotionalWhenFinalTwoDiffer : Bool
    tppPreservesEveryFirstPreferenceDistinction : Bool
    tppEqualsLiteralPoliticalDuopoly : Bool
    binaryObservationEqualsBinaryPoliticalOntology : Bool

canonicalAustralianTPPObservationBoundary : AustralianTPPObservationBoundary
canonicalAustralianTPPObservationBoundary =
  australianTPPObservationBoundary true true false false false
