module DASHI.Governance.SituatedEffectiveChoiceExact where

------------------------------------------------------------------------
-- SITUATED EFFECTIVE CHOICE
--
-- National/formal plurality does not imply local effective plurality.
-- Choice is indexed by subject, place, time, resource budget and provider
-- accessibility.  This extends EffectiveChoiceConcentrationExact rather than
-- replacing it.
--
-- Sources / bounded roles:
--
-- Northern Territory Government, Department of Health,
-- "NT Market Basket Survey 2019" and "NT Market Basket Survey 2023".
-- Official repeated survey datasets; no DOI asserted.
-- Source role: remote-store food price/availability comparison through a
-- methodologically repeated market-basket instrument.  These sources do not
-- make provider concentration the sole cause of remote price differences.
--
-- Australian Competition and Consumer Commission,
-- Supermarkets Inquiry 2024-25 / final-report public materials.
-- Institution: ACCC. No DOI asserted.
-- Source role: remote areas can have limited/no supermarket choice and higher
-- freight costs are an important explanatory driver; competition remains a
-- separate coordinate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record Situation : Set where
  constructor situation
  field
    subjectId : Nat
    placeId : Nat
    timeId : Nat

record ChoiceResources : Set where
  constructor choiceResources
  field
    transportCapacity : Nat
    moneyCapacity : Nat
    timeCapacity : Nat

record ProviderDemand : Set where
  constructor providerDemand
  field
    transportDemand : Nat
    moneyDemand : Nat
    timeDemand : Nat

record Reachable (demand : ProviderDemand) (resources : ChoiceResources) : Set where
  constructor reachable
  field
    transportWithin : ProviderDemand.transportDemand demand ≤ ChoiceResources.transportCapacity resources
    moneyWithin : ProviderDemand.moneyDemand demand ≤ ChoiceResources.moneyCapacity resources
    timeWithin : ProviderDemand.timeDemand demand ≤ ChoiceResources.timeCapacity resources

urbanResources : ChoiceResources
urbanResources = choiceResources 5 5 5

remoteResources : ChoiceResources
remoteResources = choiceResources 1 3 3

nearProvider : ProviderDemand
nearProvider = providerDemand 1 2 2

farProvider : ProviderDemand
farProvider = providerDemand 4 2 2

urbanCanReachFarProvider : Reachable farProvider urbanResources
urbanCanReachFarProvider = reachable (s≤s (s≤s (s≤s (s≤s z≤n)))) (s≤s (s≤s z≤n)) (s≤s (s≤s z≤n))

remoteCannotReachFarProvider : Reachable farProvider remoteResources → ⊥
remoteCannotReachFarProvider r = impossible (Reachable.transportWithin r)
  where
    impossible : 4 ≤ 1 → ⊥
    impossible ()

data NationalPluralityPromotesLocalPlurality : Set where

data RemotePriceGapPromotesSingleCause : Set where

data GeographicScarcityPromotesCoercion : Set where

nationalPluralityDoesNotPromoteLocalPlurality : NationalPluralityPromotesLocalPlurality → ⊥
nationalPluralityDoesNotPromoteLocalPlurality ()

remotePriceGapDoesNotPromoteSingleCause : RemotePriceGapPromotesSingleCause → ⊥
remotePriceGapDoesNotPromoteSingleCause ()

geographicScarcityDoesNotPromoteCoercion : GeographicScarcityPromotesCoercion → ⊥
geographicScarcityDoesNotPromoteCoercion ()

record SituatedEffectiveChoiceBoundary : Set where
  constructor situatedEffectiveChoiceBoundary
  field
    nationalPluralityEqualsLocalEffectivePlurality : Bool
    geographyCanChangeReachableOptionSet : Bool
    freightAndCompetitionMustRemainSeparateCauses : Bool
    unequalFeasibleChoiceFieldsCanExist : Bool
    localScarcityEqualsCoercion : Bool

canonicalSituatedEffectiveChoiceBoundary : SituatedEffectiveChoiceBoundary
canonicalSituatedEffectiveChoiceBoundary =
  situatedEffectiveChoiceBoundary false true true true false
