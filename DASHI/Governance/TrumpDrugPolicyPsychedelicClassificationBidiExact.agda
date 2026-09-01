module DASHI.Governance.TrumpDrugPolicyPsychedelicClassificationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- TRUMP-ERA DRUG-POLICY CLASSIFICATION BIDI
--
-- Source-bounded 2026 policy surface.  The same broad drug/psychoactive domain
-- is not governed by one undifferentiated rule: illicit supply, approved or
-- investigational psychedelic therapy, veteran clinical research, commercial
-- products and Indigenous/ceremonial authority can be routed through different
-- institutional classifications.  This module records that classification
-- bifurcation without promoting an ideological motive or a complete theory of
-- Trumpism.
------------------------------------------------------------------------

data PolicyActor : Set where
  donaldTrump
  saraCarter
  robertFKennedyJr
  martyMakary
  dougCollins
  namedPolicyActor : String → PolicyActor

data DrugGovernanceRoute : Set where
  punitiveIllicitSupplyRoute
  therapeuticResearchRoute
  veteranClinicalTrialRoute
  regulatedMedicalAccessRoute
  commercialConsumerProductRoute
  indigenousCeremonialAuthorityRoute
  : DrugGovernanceRoute

data PolicySurface : Set where
  nationalDrugControlStrategy2026
  psychedelicMentalHealthExecutiveOrder2026
  vaPsilocybinTrial2026
  vaMDMATrial2026
  fdaPsychedelicGuidance2026
  : PolicySurface

record SourceBoundPolicyObservation : Set where
  constructor sourceBoundPolicyObservation
  field
    surface : PolicySurface
    primaryActor : PolicyActor
    route : DrugGovernanceRoute
    sourceReference : String
    sourceDateReference : String
    ideologicalMotiveProven : Bool
    ideologicalMotiveProvenIsFalse : ideologicalMotiveProven ≡ false

open SourceBoundPolicyObservation public

nationalStrategyObservation : SourceBoundPolicyObservation
nationalStrategyObservation = sourceBoundPolicyObservation
  nationalDrugControlStrategy2026
  saraCarter
  punitiveIllicitSupplyRoute
  "White House / ONDCP 2026 National Drug Control Strategy; supply interdiction and enforcement route"
  "4 May 2026"
  false refl

psychedelicExecutiveOrderObservation : SourceBoundPolicyObservation
psychedelicExecutiveOrderObservation = sourceBoundPolicyObservation
  psychedelicMentalHealthExecutiveOrder2026
  donaldTrump
  therapeuticResearchRoute
  "White House Executive Order: Accelerating Medical Treatments for Serious Mental Illness"
  "18 April 2026"
  false refl

vaPsilocybinObservation : SourceBoundPolicyObservation
vaPsilocybinObservation = sourceBoundPolicyObservation
  vaPsilocybinTrial2026
  dougCollins
  veteranClinicalTrialRoute
  "Department of Veterans Affairs PIVOT psilocybin trial for treatment-resistant depression including concurrent PTSD"
  "5 August 2026"
  false refl

vaMDMAObservation : SourceBoundPolicyObservation
vaMDMAObservation = sourceBoundPolicyObservation
  vaMDMATrial2026
  dougCollins
  veteranClinicalTrialRoute
  "Department of Veterans Affairs randomized MDMA-assisted therapy trial for PTSD and alcohol use disorder"
  "26 May 2026"
  false refl

fdaGuidanceObservation : SourceBoundPolicyObservation
fdaGuidanceObservation = sourceBoundPolicyObservation
  fdaPsychedelicGuidance2026
  martyMakary
  regulatedMedicalAccessRoute
  "FDA final guidance: Psychedelic Drugs: Considerations for Clinical Investigations"
  "July 2026"
  false refl

------------------------------------------------------------------------
-- Classification is context-sensitive.  A punitive route does not imply that
-- every psychoactive substance/use is prohibited, and a therapeutic route does
-- not repeal the broader prohibition/enforcement regime.
------------------------------------------------------------------------

data RoutePromotesUniformDrugPolicy : Set where

data TherapeuticExceptionPromotesWarOnDrugsEnd : Set where

data PunitiveStrategyPromotesPsychedelicProhibition : Set where

routeDoesNotPromoteUniformPolicy : RoutePromotesUniformDrugPolicy → ⊥
routeDoesNotPromoteUniformPolicy ()

therapeuticExceptionDoesNotPromoteWarOnDrugsEnd :
  TherapeuticExceptionPromotesWarOnDrugsEnd → ⊥
therapeuticExceptionDoesNotPromoteWarOnDrugsEnd ()

punitiveStrategyDoesNotPromotePsychedelicProhibition :
  PunitiveStrategyPromotesPsychedelicProhibition → ⊥
punitiveStrategyDoesNotPromotePsychedelicProhibition ()

record TrumpDrugPolicyClassificationBoundary : Set where
  constructor trumpDrugPolicyClassificationBoundary
  field
    punitiveAndTherapeuticRoutesCanCoexist : Bool
    punitiveAndTherapeuticRoutesCanCoexistIsTrue :
      punitiveAndTherapeuticRoutesCanCoexist ≡ true
    veteranStatusCanDefineDistinctClinicalRoute : Bool
    veteranStatusCanDefineDistinctClinicalRouteIsTrue :
      veteranStatusCanDefineDistinctClinicalRoute ≡ true
    onePolicySurfaceProvesCompleteTrumpism : Bool
    onePolicySurfaceProvesCompleteTrumpismIsFalse :
      onePolicySurfaceProvesCompleteTrumpism ≡ false
    policyClassificationProvesActorMotive : Bool
    policyClassificationProvesActorMotiveIsFalse :
      policyClassificationProvesActorMotive ≡ false
    therapeuticPsychedelicRouteEndsPunitiveDrugGovernance : Bool
    therapeuticPsychedelicRouteEndsPunitiveDrugGovernanceIsFalse :
      therapeuticPsychedelicRouteEndsPunitiveDrugGovernance ≡ false

canonicalTrumpDrugPolicyClassificationBoundary :
  TrumpDrugPolicyClassificationBoundary
canonicalTrumpDrugPolicyClassificationBoundary =
  trumpDrugPolicyClassificationBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
