module DASHI.Core.OperationalSystemBehaviourSemanticsExact where

------------------------------------------------------------------------
-- OPERATIONAL SYSTEM BEHAVIOUR SEMANTICS
--
-- Stafford Beer's POSIWID heuristic ("the purpose of a system is what it
-- does") motivates privileging observed operation over charitable mission-
-- statement reconstruction when describing a system's realised behaviour.
--
-- Source boundary: Beer supplies the cybernetic heuristic.  The typed records,
-- finite counterexamples and factorisation theorems below are DASHI machinery,
-- not mathematics attributed to Beer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.DeclaredRealizedIntegrityResidualExact as DeclaredRealized

record OperationalSystem
    (State Declared Behaviour Effect Correction : Set) : Set₁ where
  constructor operational-system
  field
    declaredPurpose : State → Declared
    operationalBehaviour : State → Behaviour
    realizedEffect : State → Effect
    correctionResponse : State → Correction

open OperationalSystem public

------------------------------------------------------------------------
-- Same declared purpose can coexist with distinct realised operation/effect.
------------------------------------------------------------------------

data DemoState : Set where
  declaredSameRealizedOpen : DemoState
  declaredSameRealizedClosed : DemoState


data DemoDeclared : Set where
  sameDeclaredPurpose : DemoDeclared

data DemoBehaviour : Set where
  openBehaviour : DemoBehaviour
  closedBehaviour : DemoBehaviour

data DemoEffect : Set where
  openEffect : DemoEffect
  closedEffect : DemoEffect

data DemoCorrection : Set where
  acceptsCorrection : DemoCorrection
  convertsCorrectionToFault : DemoCorrection

demoDeclared : DemoState → DemoDeclared
demoDeclared declaredSameRealizedOpen = sameDeclaredPurpose
demoDeclared declaredSameRealizedClosed = sameDeclaredPurpose

demoBehaviour : DemoState → DemoBehaviour
demoBehaviour declaredSameRealizedOpen = openBehaviour
demoBehaviour declaredSameRealizedClosed = closedBehaviour

demoEffect : DemoState → DemoEffect
demoEffect declaredSameRealizedOpen = openEffect
demoEffect declaredSameRealizedClosed = closedEffect

demoCorrection : DemoState → DemoCorrection
demoCorrection declaredSameRealizedOpen = acceptsCorrection
demoCorrection declaredSameRealizedClosed = convertsCorrectionToFault

demoSystem : OperationalSystem DemoState DemoDeclared DemoBehaviour DemoEffect DemoCorrection
demoSystem = operational-system demoDeclared demoBehaviour demoEffect demoCorrection

effectsDiffer :
  demoEffect declaredSameRealizedOpen ≡ demoEffect declaredSameRealizedClosed → ⊥
effectsDiffer ()

behavioursDiffer :
  demoBehaviour declaredSameRealizedOpen ≡ demoBehaviour declaredSameRealizedClosed → ⊥
behavioursDiffer ()

correctionResponsesDiffer :
  demoCorrection declaredSameRealizedOpen ≡ demoCorrection declaredSameRealizedClosed → ⊥
correctionResponsesDiffer ()

declaredPurposeEffectWitness : INF.NonFactorabilityWitness demoDeclared demoEffect
declaredPurposeEffectWitness =
  INF.nonFactorabilityWitness
    declaredSameRealizedOpen
    declaredSameRealizedClosed
    refl
    effectsDiffer

declaredPurposeBehaviourWitness : INF.NonFactorabilityWitness demoDeclared demoBehaviour
declaredPurposeBehaviourWitness =
  INF.nonFactorabilityWitness
    declaredSameRealizedOpen
    declaredSameRealizedClosed
    refl
    behavioursDiffer

declaredPurposeCorrectionWitness : INF.NonFactorabilityWitness demoDeclared demoCorrection
declaredPurposeCorrectionWitness =
  INF.nonFactorabilityWitness
    declaredSameRealizedOpen
    declaredSameRealizedClosed
    refl
    correctionResponsesDiffer

declaredPurposeCannotRecoverRealizedEffect :
  INF.FactorsThrough demoDeclared demoEffect → ⊥
declaredPurposeCannotRecoverRealizedEffect =
  INF.witnessRulesOutEveryFlatFactorisation declaredPurposeEffectWitness

declaredPurposeCannotRecoverOperationalBehaviour :
  INF.FactorsThrough demoDeclared demoBehaviour → ⊥
declaredPurposeCannotRecoverOperationalBehaviour =
  INF.witnessRulesOutEveryFlatFactorisation declaredPurposeBehaviourWitness

declaredPurposeCannotRecoverCorrectionResponse :
  INF.FactorsThrough demoDeclared demoCorrection → ⊥
declaredPurposeCannotRecoverCorrectionResponse =
  INF.witnessRulesOutEveryFlatFactorisation declaredPurposeCorrectionWitness

------------------------------------------------------------------------
-- Intent, legitimacy and ontology remain distinct from operational description.
------------------------------------------------------------------------

data Intent : Set where
  benignIntent : Intent
  hostileIntent : Intent
  unknownIntent : Intent

data Legitimacy : Set where
  legitimate : Legitimacy
  illegitimate : Legitimacy
  contestedLegitimacy : Legitimacy

record OperationalDescriptionBoundary : Set where
  constructor operational-description-boundary
  field
    observedOperationMayClassifyWhatSystemDoes : Bool
    observedOperationMayClassifyWhatSystemDoesIsTrue :
      observedOperationMayClassifyWhatSystemDoes ≡ true
    observedOperationProvesSubjectiveIntent : Bool
    observedOperationProvesSubjectiveIntentIsFalse :
      observedOperationProvesSubjectiveIntent ≡ false
    declaredPurposeOverridesRepeatedRealizedEffect : Bool
    declaredPurposeOverridesRepeatedRealizedEffectIsFalse :
      declaredPurposeOverridesRepeatedRealizedEffect ≡ false
    operationalDescriptionProvesLegitimacy : Bool
    operationalDescriptionProvesLegitimacyIsFalse :
      operationalDescriptionProvesLegitimacy ≡ false
    operationalDescriptionIsWorldCompleteOntology : Bool
    operationalDescriptionIsWorldCompleteOntologyIsFalse :
      operationalDescriptionIsWorldCompleteOntology ≡ false
    correctionResponseIsPartOfObservableOperation : Bool
    correctionResponseIsPartOfObservableOperationIsTrue :
      correctionResponseIsPartOfObservableOperation ≡ true

open OperationalDescriptionBoundary public

canonicalOperationalDescriptionBoundary : OperationalDescriptionBoundary
canonicalOperationalDescriptionBoundary =
  operational-description-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- POSIWID provenance firewall.
------------------------------------------------------------------------

record POSIWIDSourceBoundary : Set where
  constructor posiwid-source-boundary
  field
    sourceAuthor : String
    heuristicReference : String
    sourceRole : String
    heuristicPrioritisesObservedOperation : Bool
    heuristicPrioritisesObservedOperationIsTrue :
      heuristicPrioritisesObservedOperation ≡ true
    heuristicAutomaticallyProvesIntent : Bool
    heuristicAutomaticallyProvesIntentIsFalse :
      heuristicAutomaticallyProvesIntent ≡ false
    heuristicAutomaticallyProvesLegitimacy : Bool
    heuristicAutomaticallyProvesLegitimacyIsFalse :
      heuristicAutomaticallyProvesLegitimacy ≡ false
    beerAuthoredDASHIFactorisationTheorem : Bool
    beerAuthoredDASHIFactorisationTheoremIsFalse :
      beerAuthoredDASHIFactorisationTheorem ≡ false

open POSIWIDSourceBoundary public

canonicalPOSIWIDSourceBoundary : POSIWIDSourceBoundary
canonicalPOSIWIDSourceBoundary =
  posiwid-source-boundary
    "Stafford Beer"
    "POSIWID: the purpose of a system is what it does; Heart of Enterprise (1979), later public formulations including Valladolid 2001 / Kybernetes publication"
    "cybernetic heuristic for starting from realised operation rather than declared benevolent purpose"
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Existing declared/realised owner remains a direct structural neighbour.
------------------------------------------------------------------------

declaredRealizedMismatchDoesNotProveIntent :
  DeclaredRealized.realizedMismatchProvesHostileIntent
    DeclaredRealized.canonicalDeclaredRealizedBoundary ≡ false
declaredRealizedMismatchDoesNotProveIntent = refl

------------------------------------------------------------------------
-- No-promotion laws.
------------------------------------------------------------------------

data MissionStatementDeterminesSystemEffect : Set where
data POSIWIDProvesHostileIntent : Set where
data POSIWIDProvesMoralLegitimacy : Set where
data CorrectionAttemptIsExternalToSystemBehaviour : Set where

missionStatementDoesNotDetermineEffect : MissionStatementDeterminesSystemEffect → ⊥
missionStatementDoesNotDetermineEffect ()

posiwidDoesNotProveHostileIntent : POSIWIDProvesHostileIntent → ⊥
posiwidDoesNotProveHostileIntent ()

posiwidDoesNotProveLegitimacy : POSIWIDProvesMoralLegitimacy → ⊥
posiwidDoesNotProveLegitimacy ()

correctionHandlingIsObservableSystemBehaviour : CorrectionAttemptIsExternalToSystemBehaviour → ⊥
correctionHandlingIsObservableSystemBehaviour ()
