module DASHI.Dynamics.ConcreteCoalitionPopulationDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

data _⊎_ (X Y : Set) : Set where
  inj₁ : X → X ⊎ B
  inj₂ : Y → X ⊎ Y

data Competitor : Set where
  A B : Competitor

data PartnerState : Set where
  unpaired paired : PartnerState

record PopulationProfile : Set where
  constructor profile
  field
    competitor : Competitor
    partnerState : PartnerState

open PopulationProfile public

AA AB BA BB : PopulationProfile
AA = profile A unpaired
AB = profile A paired
BA = profile B unpaired
BB = profile B paired

fitness : PopulationProfile → Nat
fitness AA = 1
fitness AB = 3
fitness BA = 2
fitness BB = 3

select : PopulationProfile → PopulationProfile
select AA = AB
select AB = AB
select BA = BB
select BB = BB

mutatePartner : PopulationProfile → PopulationProfile
mutatePartner AA = AB
mutatePartner AB = AA
mutatePartner BA = BB
mutatePartner BB = BA

mutateCompetitor : PopulationProfile → PopulationProfile
mutateCompetitor AA = BA
mutateCompetitor AB = BB
mutateCompetitor BA = AA
mutateCompetitor BB = AB

selectionIdempotent :
  (p : PopulationProfile) →
  select (select p) ≡ select p
selectionIdempotent AA = refl
selectionIdempotent AB = refl
selectionIdempotent BA = refl
selectionIdempotent BB = refl

partnerMutationInvolutive :
  (p : PopulationProfile) →
  mutatePartner (mutatePartner p) ≡ p
partnerMutationInvolutive AA = refl
partnerMutationInvolutive AB = refl
partnerMutationInvolutive BA = refl
partnerMutationInvolutive BB = refl

competitorMutationInvolutive :
  (p : PopulationProfile) →
  mutateCompetitor (mutateCompetitor p) ≡ p
competitorMutationInvolutive AA = refl
competitorMutationInvolutive AB = refl
competitorMutationInvolutive BA = refl
competitorMutationInvolutive BB = refl

data OrbitClass : Set where
  fixedA fixedB : OrbitClass

classifySelectionOrbit : PopulationProfile → OrbitClass
classifySelectionOrbit AA = fixedA
classifySelectionOrbit AB = fixedA
classifySelectionOrbit BA = fixedB
classifySelectionOrbit BB = fixedB

selectionReachesRepresentative :
  (p : PopulationProfile) →
  (select p ≡ AB) ⊎ (select p ≡ BB)
selectionReachesRepresentative AA = inj₁ refl
selectionReachesRepresentative AB = inj₁ refl
selectionReachesRepresentative BA = inj₂ refl
selectionReachesRepresentative BB = inj₂ refl

data SelectionTrit : Set where
  negative neutral positive : SelectionTrit

encodeSelectionTrit : PopulationProfile → SelectionTrit
encodeSelectionTrit AA = negative
encodeSelectionTrit AB = positive
encodeSelectionTrit BA = negative
encodeSelectionTrit BB = positive

record LogisticComparisonAuthority : Set₁ where
  field
    RealState : Set
    Parameter : Set
    logisticStep : Parameter → RealState → RealState
    firstPeriodDoublingAtThree : Set
    selectedInvariantMeasure : Set
    symbolicItinerarySound : Set
    finitePopulationComparison : Set

record CoalitionPopulationReceipt : Set where
  constructor mkCoalitionPopulationReceipt
  field
    fourProfilesChecked : Bool
    explicitFitnessChecked : Bool
    selectionOperatorChecked : Bool
    mutationOperatorsChecked : Bool
    selectionOrbitClassified : Bool
    symbolicTriadicEncodingChecked : Bool
    finiteReferenceIsAnalyticLogisticMap : Bool
    finiteReferenceIsAnalyticLogisticMapIsFalse :
      finiteReferenceIsAnalyticLogisticMap ≡ false
    decimalDigitsCauseBifurcation : Bool
    decimalDigitsCauseBifurcationIsFalse :
      decimalDigitsCauseBifurcation ≡ false
    interpretation : String

coalitionPopulationReceipt : CoalitionPopulationReceipt
coalitionPopulationReceipt =
  mkCoalitionPopulationReceipt
    true true true true true true false refl false refl
    "the C2 by C2 population/partner carrier has executable selection, mutation, payoff and orbit laws; comparison with the real logistic map requires an explicit analytic authority and symbolic-itinerary proof"
