module DASHI.Governance.ResponsiveInfluencePolicy where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

------------------------------------------------------------------------
-- Separate content from the policy that selects the next content.
--
-- This keeps screens, food, schooling, religion, advertising, platforms and
-- caregiving as possible instances without equating their psychological
-- mechanisms or normative status.
------------------------------------------------------------------------

record InfluenceSystem : Set₁ where
  field
    State : Set
    Input : Set
    Feedback : Set
    Objective : Set
    History : Set

    select : State → History → Feedback → Objective → Input
    update : State → Input → State
    extendHistory : History → Input → Feedback → History

open InfluenceSystem public

record ResponsiveInfluence
  (S : InfluenceSystem) : Set₁ where
  field
    childState : State S
    history : History S
    feedback : Feedback S
    objective : Objective S
    selectedInput : Input S
    selectionTracksStateAndFeedback :
      select S childState history feedback objective ≡ selectedInput

record ExternalObjectiveInfluence
  (S : InfluenceSystem) : Set₁ where
  field
    state : State S
    history : History S
    feedback : Feedback S
    welfareObjective : Objective S
    externalObjective : Objective S
    selectedInput : Input S
    objectiveDiverges : ¬ (externalObjective ≡ welfareObjective)
    selectionUsesExternalObjective :
      select S state history feedback externalObjective ≡ selectedInput

------------------------------------------------------------------------
-- Optimising a proxy is not a theorem that welfare is optimised.
------------------------------------------------------------------------

data ProxyOptimalityEstablishesWelfareOptimality : Set where

proxyOptimalityDoesNotEstablishWelfareOptimality :
  ProxyOptimalityEstablishesWelfareOptimality → ⊥
proxyOptimalityDoesNotEstablishWelfareOptimality ()

record ProxyObjectiveBoundary : Set where
  constructor proxyObjectiveBoundary
  field
    engagementEqualsWelfare : Bool
    repeatPurchaseEqualsWelfare : Bool
    complianceEqualsWelfare : Bool
    behaviouralQuietEqualsWelfare : Bool
    objectiveMustBeMadeExplicit : Bool
    subjectFeedbackMustRemainRepresented : Bool

canonicalProxyObjectiveBoundary : ProxyObjectiveBoundary
canonicalProxyObjectiveBoundary =
  proxyObjectiveBoundary false false false false true true

------------------------------------------------------------------------
-- Caregiver constraint geometry.
--
-- Feasible policy sets can be restricted by time, money, sleep, childcare,
-- attention and social support.  This blocks the formal model from converting
-- structural constraint into a parent-blame theorem.
------------------------------------------------------------------------

record CaregiverConstraintSystem : Set₁ where
  field
    Caregiver : Set
    ResourceBudget : Set
    Policy : Set
    feasible : Caregiver → ResourceBudget → Policy → Set

record ConstrainedCaregivingChoice
  (S : CaregiverConstraintSystem) : Set₁ where
  field
    caregiver : Caregiver S
    budget : ResourceBudget S
    chosenPolicy : Policy S
    chosenPolicyFeasible : feasible S caregiver budget chosenPolicy


data ConstraintEstablishesNeglect : Set where

constraintAloneDoesNotEstablishNeglect : ConstraintEstablishesNeglect → ⊥
constraintAloneDoesNotEstablishNeglect ()

record ResponsiveInfluenceReceipt : Set where
  constructor responsiveInfluenceReceipt
  field
    label : String
    sourceAtlas : List Sources.ScholarlySource
    contextNotScalarTimeAlone : Bool
    contentSeparatedFromSelectionPolicy : Bool
    externalObjectiveSeparatedFromWelfare : Bool
    structuralConstraintSeparatedFromParentalMotive : Bool

canonicalResponsiveInfluenceReceipt : ResponsiveInfluenceReceipt
canonicalResponsiveInfluenceReceipt =
  responsiveInfluenceReceipt
    "responsive influence / external objective boundary"
    (Sources.screenUseContextMetaAnalysis
      ∷ Sources.feedingPracticesProspective
      ∷ [])
    true true true true
