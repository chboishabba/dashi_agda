module DASHI.Reasoning.PathologicConstraintSystem where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Source calibration:
--
-- * Harris Brewis (hbomberguy), "Pathologic is Genius, And Here's Why",
--   YouTube video essay, 21 November 2019, no DOI.
-- * Julian Novitz, "Scarcity and Survival Horror: Trade as an Instrument of
--   Terror in Pathologic", Transactions of the Digital Games Research
--   Association 3(1), 2017, DOI 10.26503/todigra.v3i1.64.
--
-- The formal carrier separates an action constructor from the dependent
-- evidence needed to attempt it under time, body, reputation and role limits.
------------------------------------------------------------------------

data Doctor : Set where
  bachelor haruspex changeling : Doctor

data PathologicAction : Set where
  walk converse trade fight rest readLetters investigate : PathologicAction
  laboratoryInference dissectCorpse miracleHeal treatInfected : PathologicAction

record ActionCost : Set where
  field
    timeCost : Nat
    healthCost : Nat
    reputationThreshold : Nat
    infectionExposure : Nat
    hungerIncrease : Nat
    exhaustionIncrease : Nat

open ActionCost public

actionCost : PathologicAction → ActionCost
actionCost walk = record
  { timeCost = 1 ; healthCost = 0 ; reputationThreshold = 0
  ; infectionExposure = 0 ; hungerIncrease = 1 ; exhaustionIncrease = 1 }
actionCost converse = record
  { timeCost = 1 ; healthCost = 0 ; reputationThreshold = 0
  ; infectionExposure = 0 ; hungerIncrease = 0 ; exhaustionIncrease = 0 }
actionCost trade = record
  { timeCost = 1 ; healthCost = 0 ; reputationThreshold = 1
  ; infectionExposure = 0 ; hungerIncrease = 0 ; exhaustionIncrease = 0 }
actionCost fight = record
  { timeCost = 1 ; healthCost = 2 ; reputationThreshold = 0
  ; infectionExposure = 0 ; hungerIncrease = 1 ; exhaustionIncrease = 2 }
actionCost rest = record
  { timeCost = 2 ; healthCost = 0 ; reputationThreshold = 0
  ; infectionExposure = 0 ; hungerIncrease = 2 ; exhaustionIncrease = 0 }
actionCost readLetters = record
  { timeCost = 0 ; healthCost = 0 ; reputationThreshold = 0
  ; infectionExposure = 0 ; hungerIncrease = 0 ; exhaustionIncrease = 0 }
actionCost investigate = record
  { timeCost = 2 ; healthCost = 0 ; reputationThreshold = 1
  ; infectionExposure = 1 ; hungerIncrease = 1 ; exhaustionIncrease = 1 }
actionCost laboratoryInference = record
  { timeCost = 2 ; healthCost = 0 ; reputationThreshold = 1
  ; infectionExposure = 0 ; hungerIncrease = 0 ; exhaustionIncrease = 1 }
actionCost dissectCorpse = record
  { timeCost = 2 ; healthCost = 0 ; reputationThreshold = 0
  ; infectionExposure = 2 ; hungerIncrease = 0 ; exhaustionIncrease = 1 }
actionCost miracleHeal = record
  { timeCost = 1 ; healthCost = 2 ; reputationThreshold = 0
  ; infectionExposure = 2 ; hungerIncrease = 0 ; exhaustionIncrease = 1 }
actionCost treatInfected = record
  { timeCost = 2 ; healthCost = 1 ; reputationThreshold = 0
  ; infectionExposure = 2 ; hungerIncrease = 0 ; exhaustionIncrease = 1 }

data RoleCapability : Doctor → PathologicAction → Set where
  canWalk : ∀ {doctor} → RoleCapability doctor walk
  canConverse : ∀ {doctor} → RoleCapability doctor converse
  canTrade : ∀ {doctor} → RoleCapability doctor trade
  canFight : ∀ {doctor} → RoleCapability doctor fight
  canRest : ∀ {doctor} → RoleCapability doctor rest
  canReadLetters : ∀ {doctor} → RoleCapability doctor readLetters
  canInvestigate : ∀ {doctor} → RoleCapability doctor investigate
  canTreat : ∀ {doctor} → RoleCapability doctor treatInfected
  bachelorCanInfer : RoleCapability bachelor laboratoryInference
  haruspexCanDissect : RoleCapability haruspex dissectCorpse
  changelingCanMiracleHeal : RoleCapability changeling miracleHeal

record TownState : Set where
  field
    activeDoctor : Doctor
    dayIndex : Nat
    timeRemaining : Nat
    health : Nat
    hunger : Nat
    exhaustion : Nat
    reputation : Nat
    infection : Nat
    immunity : Nat
    money : Nat
    unreadLetters : Nat
    boundAtRisk : Nat

open TownState public

record ActionDependency
    (state : TownState)
    (action : PathologicAction) : Set where
  field
    enoughTime : timeCost (actionCost action) ≤ timeRemaining state
    enoughHealth : healthCost (actionCost action) ≤ health state
    enoughReputation :
      reputationThreshold (actionCost action) ≤ reputation state
    roleCapability : RoleCapability (activeDoctor state) action
    dependencyReceipt : String

open ActionDependency public

record ActionTransitionReceipt
    (before : TownState)
    (action : PathologicAction)
    (after : TownState) : Set where
  field
    timeCostApplied : Bool
    bodyCostApplied : Bool
    infectionRiskApplied : Bool
    reputationEffectRetained : Bool
    transitionReceipt : String

actionName : PathologicAction → String
actionName walk = "walk"
actionName converse = "converse"
actionName trade = "trade"
actionName fight = "fight"
actionName rest = "rest"
actionName readLetters = "read letters"
actionName investigate = "investigate"
actionName laboratoryInference = "laboratory inference"
actionName dissectCorpse = "dissect corpse"
actionName miracleHeal = "miracle heal"
actionName treatInfected = "treat infected"

pathologicActionSystem :
  Dependency.DependentActionSystem TownState PathologicAction
pathologicActionSystem = record
  { Precondition = ActionDependency
  ; Postcondition = ActionTransitionReceipt
  ; actionLabel = actionName
  }

canonicalBachelorState : TownState
canonicalBachelorState = record
  { activeDoctor = bachelor
  ; dayIndex = 1
  ; timeRemaining = 12
  ; health = 10
  ; hunger = 0
  ; exhaustion = 0
  ; reputation = 5
  ; infection = 0
  ; immunity = 5
  ; money = 10
  ; unreadLetters = 1
  ; boundAtRisk = 0
  }

canonicalBachelorWalkDependency :
  ActionDependency canonicalBachelorState walk
canonicalBachelorWalkDependency = record
  { enoughTime = s≤s z≤n
  ; enoughHealth = z≤n
  ; enoughReputation = z≤n
  ; roleCapability = canWalk
  ; dependencyReceipt =
      "Walking is inhabited and currently admissible, but consumes scarce time and modifies the survival ledger."
  }

------------------------------------------------------------------------
-- Opaque requirements: a dependency may be operationally mandatory even when
-- the interface does not disclose it adequately.
------------------------------------------------------------------------

data CoreMechanic : Set where
  mailMechanic inventoryCapacityMechanic dialogueExitMechanic : CoreMechanic

record OpaqueMechanicDependency : Set where
  field
    mechanic : CoreMechanic
    requiredForProgress : Bool
    dependencyWitnessAvailable : Bool
    tutorialDisclosurePresent : Bool
    nonDisclosureArtisticallyRequired : Bool
    implementationDefectStillPossible : Bool
    disclosureReceipt : String

mailDependencyReceipt : OpaqueMechanicDependency
mailDependencyReceipt = record
  { mechanic = mailMechanic
  ; requiredForProgress = true
  ; dependencyWitnessAvailable = true
  ; tutorialDisclosurePresent = false
  ; nonDisclosureArtisticallyRequired = false
  ; implementationDefectStillPossible = true
  ; disclosureReceipt =
      "The review distinguishes productive uncertainty from failure to disclose the story-critical letters interface."
  }

------------------------------------------------------------------------
-- Scarcity shock and recontextualisation.
------------------------------------------------------------------------

data EconomyPhase : Set where
  ordinaryExchange scarcityShock : EconomyPhase

priceMultiplier : EconomyPhase → Nat
priceMultiplier ordinaryExchange = 1
priceMultiplier scarcityShock = 10

dayTwoPriceMultiplierIsTen :
  priceMultiplier scarcityShock ≡ 10
dayTwoPriceMultiplierIsTen = refl

data Mechanic : Set where
  moneyMechanic foodMechanic walkingMechanic combatMechanic dialogueMechanic : Mechanic

data MechanicReading : Set where
  ordinaryAffordance survivalConstraint moralPressure epistemicTrap : MechanicReading

record RecontextualisedMechanic : Set where
  field
    mechanic : Mechanic
    priorReading : MechanicReading
    laterReading : MechanicReading
    stateChangeReceipt : String
    mechanicImplementationChanged : Bool
    playerRelationChanged : Bool

canonicalMoneyRecontextualisation : RecontextualisedMechanic
canonicalMoneyRecontextualisation = record
  { mechanic = moneyMechanic
  ; priorReading = ordinaryAffordance
  ; laterReading = survivalConstraint
  ; stateChangeReceipt =
      "The day-two scarcity shock changes what money means to the player without changing the basic shop interaction."
  ; mechanicImplementationChanged = false
  ; playerRelationChanged = true
  }

data FrictionOrigin : Set where
  authoredConstraint implementationDefect budgetCompromise unresolvedFriction : FrictionOrigin

record FrictionClassification : Set where
  field
    frictionLabel : String
    origin : FrictionOrigin
    evidenceReceipt : String
    negativeExperienceArtisticallyProductive : Bool
    defectExcusedByInterpretation : Bool

record PathologicConstraintAuthorityBoundary : Set where
  field
    actionConstructorEqualsAdmissibilityWitness : Bool
    feasibilityEqualsPrudence : Bool
    feasibilityEqualsMoralPermission : Bool
    everyUnpleasantMechanicIsIntentional : Bool
    everyTechnicalDefectIsArtisticallyNecessary : Bool
    noSingleScalarUtilityAssumed : Bool
    roleSpecificCapabilitiesTyped : Bool
    timeBodyReputationDependenciesTyped : Bool
    boundaryNote : String

canonicalPathologicConstraintAuthorityBoundary :
  PathologicConstraintAuthorityBoundary
canonicalPathologicConstraintAuthorityBoundary = record
  { actionConstructorEqualsAdmissibilityWitness = false
  ; feasibilityEqualsPrudence = false
  ; feasibilityEqualsMoralPermission = false
  ; everyUnpleasantMechanicIsIntentional = false
  ; everyTechnicalDefectIsArtisticallyNecessary = false
  ; noSingleScalarUtilityAssumed = true
  ; roleSpecificCapabilitiesTyped = true
  ; timeBodyReputationDependenciesTyped = true
  ; boundaryNote =
      "Pathologic is modelled as a dependent constraint field: can, should, morally may and narratively must are different types. Authored friction and jank remain separately evidenced."
  }
