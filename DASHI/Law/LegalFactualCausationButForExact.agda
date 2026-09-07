module DASHI.Law.LegalFactualCausationButForExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.CounterfactualModelContractExact as Counterfactual

------------------------------------------------------------------------
-- LEGAL FACTUAL CAUSATION / "BUT FOR" TEST
--
-- DASHI-original abstraction/compiler.
--
-- Legal propositions used to calibrate this owner are source-owned elsewhere;
-- this module does not attribute the record architecture below to a court or
-- legislature.  It reuses CounterfactualModelContractExact so an observed
-- outcome minus an arbitrary alternative cannot silently become causation.
------------------------------------------------------------------------

record BreachCorrection : Set₁ where
  constructor breachCorrection
  field
    Conduct : Set
    actualConduct : Conduct
    compliantConduct : Conduct
    actualConductBreachReceipt : Set
    compliantConductReceipt : Set
    correctionChangesBreachCoordinateReceipt : Set
    correctionReference : String

open BreachCorrection public

record LegalButForQuestion : Set₁ where
  constructor legalButForQuestion
  field
    contract : Counterfactual.CounterfactualContract
    correction : BreachCorrection

    Harm : Set
    particularHarm : Harm
    HarmOccursObserved : Set
    HarmOccursCounterfactual : Set

    observedHarmReceipt : HarmOccursObserved
    sameParticularHarmReceipt : Set
    counterfactualLegalityReceipt : Set
    legalQuestionReference : String

open LegalButForQuestion public

------------------------------------------------------------------------
-- Ordinary necessary-condition route.
--
-- The negative counterfactual is proposition-valued rather than a Boolean:
-- the ordinary route owns a proof that the particular harm cannot be shown to
-- occur in the admissible no-breach counterfactual represented by the question.
------------------------------------------------------------------------

record NecessaryConditionReceipt (q : LegalButForQuestion) : Set₁ where
  constructor necessaryConditionReceipt
  field
    harmAbsentWithoutBreach : HarmOccursCounterfactual q → ⊥
    comparisonReceipt : Set
    causalIdentificationReceipt : Set
    necessaryConditionSourceReference : String

open NecessaryConditionReceipt public

------------------------------------------------------------------------
-- Exceptional route.
--
-- This is intentionally not a disguised necessary-condition proof.  A legal
-- system may expose an exceptional established-principles route; admission of
-- that route requires its own authority and responsibility receipts.
------------------------------------------------------------------------

record ExceptionalCausationReceipt (q : LegalButForQuestion) : Set₁ where
  constructor exceptionalCausationReceipt
  field
    ordinaryNecessaryConditionNotEstablishedReceipt : Set
    establishedPrinciplesReceipt : Set
    responsibilityReasonReceipt : Set
    authorityReceipt : Set
    exceptionalRouteReference : String

open ExceptionalCausationReceipt public

data FactualCausationRoute (q : LegalButForQuestion) : Set₁ where
  ordinaryNecessaryCondition :
    NecessaryConditionReceipt q → FactualCausationRoute q
  exceptionalAcceptedCausation :
    ExceptionalCausationReceipt q → FactualCausationRoute q

record FactualCausationReceipt (q : LegalButForQuestion) : Set₁ where
  constructor factualCausationReceipt
  field
    route : FactualCausationRoute q
    adjudicativeOrResolverReference : String
    factualCausationReference : String

open FactualCausationReceipt public

------------------------------------------------------------------------
-- Scope of liability remains a separate normative/legal gate.
------------------------------------------------------------------------

record ScopeOfLiabilityReceipt
    {q : LegalButForQuestion}
    (factual : FactualCausationReceipt q) : Set₁ where
  constructor scopeOfLiabilityReceipt
  field
    harmWithinScopeReceipt : Set
    responsibilityReasons : List String
    normativeAttributionReceipt : Set
    legalAuthorityReceipt : Set
    scopeReference : String

open ScopeOfLiabilityReceipt public

------------------------------------------------------------------------
-- Counterfactual fibres.
--
-- A legal counterfactual may be underidentified.  Rather than silently select
-- a favourable world, applications can retain all admissible no-breach worlds
-- and separately prove robust absence, selected-world absence, or ambiguity.
------------------------------------------------------------------------

record NoBreachCounterfactualFibre : Set₁ where
  constructor noBreachCounterfactualFibre
  field
    World Harm : Set
    admissibleNoBreachWorld : World → Set
    particularHarm : Harm
    harmOccurs : World → Harm → Set
    fibreReference : String

open NoBreachCounterfactualFibre public

record RobustButForReceipt (f : NoBreachCounterfactualFibre) : Set₁ where
  constructor robustButForReceipt
  field
    absentInEveryAdmissibleWorld :
      (w : World f) →
      admissibleNoBreachWorld f w →
      harmOccurs f w (particularHarm f) → ⊥
    robustnessReference : String

open RobustButForReceipt public

record SelectedCounterfactualReceipt (f : NoBreachCounterfactualFibre) : Set₁ where
  constructor selectedCounterfactualReceipt
  field
    selectedWorld : World f
    selectedWorldAdmissible : admissibleNoBreachWorld f selectedWorld
    selectionJustificationReceipt : Set
    selectedWorldReference : String

open SelectedCounterfactualReceipt public

record CounterfactualUnderidentificationReceipt
    (f : NoBreachCounterfactualFibre) : Set₁ where
  constructor counterfactualUnderidentificationReceipt
  field
    harmWorld noHarmWorld : World f
    harmWorldAdmissible : admissibleNoBreachWorld f harmWorld
    noHarmWorldAdmissible : admissibleNoBreachWorld f noHarmWorld
    harmOccursInHarmWorld : harmOccurs f harmWorld (particularHarm f)
    harmAbsentInNoHarmWorld :
      harmOccurs f noHarmWorld (particularHarm f) → ⊥
    underidentificationReference : String

open CounterfactualUnderidentificationReceipt public

------------------------------------------------------------------------
-- Adjudicative proof is not causal probability.
------------------------------------------------------------------------

data LegalProofStandard : Set where
  balanceOfProbabilities
  beyondReasonableDoubt
  clearAndConvincing
  proofStandardUnresolved
  : LegalProofStandard

record CausationProofReceipt {q : LegalButForQuestion}
    (factual : FactualCausationReceipt q) : Set₁ where
  constructor causationProofReceipt
  field
    bearerReference : String
    standard : LegalProofStandard
    evidenceReferences : List String
    satisfiesStandardReceipt : Set
    proofReference : String

open CausationProofReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CounterfactualDifferenceAutomaticallyCausation : Set where
data ButForAutomaticallyScopeOfLiability : Set where
data ButForAutomaticallyLiability : Set where
data BreachAutomaticallyCausation : Set where
data CausationAutomaticallyBreach : Set where
data PossibleAvoidanceAutomaticallyLiability : Set where
data UnderidentificationAutomaticallyNoCausation : Set where
data BalanceOfProbabilitiesIsCausalProbability : Set where
data ExceptionalCausationIsOrdinaryButFor : Set where

counterfactualDifferenceDoesNotAutoCause :
  CounterfactualDifferenceAutomaticallyCausation → ⊥
counterfactualDifferenceDoesNotAutoCause ()

butForDoesNotAutoEstablishScope :
  ButForAutomaticallyScopeOfLiability → ⊥
butForDoesNotAutoEstablishScope ()

butForDoesNotAutoEstablishLiability :
  ButForAutomaticallyLiability → ⊥
butForDoesNotAutoEstablishLiability ()

breachDoesNotAutoEstablishCausation :
  BreachAutomaticallyCausation → ⊥
breachDoesNotAutoEstablishCausation ()

causationDoesNotAutoEstablishBreach :
  CausationAutomaticallyBreach → ⊥
causationDoesNotAutoEstablishBreach ()

possibleAvoidanceDoesNotAutoEstablishLiability :
  PossibleAvoidanceAutomaticallyLiability → ⊥
possibleAvoidanceDoesNotAutoEstablishLiability ()

underidentificationDoesNotMeanNoCausation :
  UnderidentificationAutomaticallyNoCausation → ⊥
underidentificationDoesNotMeanNoCausation ()

balanceOfProbabilitiesIsNotCausalProbability :
  BalanceOfProbabilitiesIsCausalProbability → ⊥
balanceOfProbabilitiesIsNotCausalProbability ()

exceptionalRouteIsNotOrdinaryButForProof :
  ExceptionalCausationIsOrdinaryButFor → ⊥
exceptionalRouteIsNotOrdinaryButForProof ()

record LegalButForBoundary : Set where
  constructor legalButForBoundary
  field
    arbitraryAlternativeIsLegalCounterfactual : Bool
    arbitraryAlternativeIsLegalCounterfactualIsFalse :
      arbitraryAlternativeIsLegalCounterfactual ≡ false
    parserCandidateCanProveCausation : Bool
    parserCandidateCanProveCausationIsFalse :
      parserCandidateCanProveCausation ≡ false
    factualCausationEqualsScopeOfLiability : Bool
    factualCausationEqualsScopeOfLiabilityIsFalse :
      factualCausationEqualsScopeOfLiability ≡ false
    exceptionalRouteMayRemainDistinct : Bool
    exceptionalRouteMayRemainDistinctIsTrue :
      exceptionalRouteMayRemainDistinct ≡ true

canonicalLegalButForBoundary : LegalButForBoundary
canonicalLegalButForBoundary =
  legalButForBoundary false refl false refl false refl true refl
