module DASHI.Core.ExperimentLanguageEquivalenceExact where

------------------------------------------------------------------------
-- A bounded experiment language is stronger than a bag of admissible actions.
-- Equivalence is quantified over declared action traces.  One admissible trace
-- whose terminal observation differs constructively refutes equivalence.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)

import DASHI.Core.GenericFuturePartitionRefinementExact as Future

record ExperimentLanguage (Action : Set) : Set₁ where
  constructor experimentLanguage
  field
    Admissible : List Action → Set

open ExperimentLanguage public

LanguageEquivalent :
  ∀ {State Action Observation} →
  ExperimentLanguage Action →
  (State → Observation) →
  (Action → State → State) →
  State → State → Set
LanguageEquivalent {Action = Action} language observe step left right =
  (actions : List Action) →
  Admissible language actions →
  observe (Future.run step actions left)
  ≡ observe (Future.run step actions right)

record AdmissibleSeparatingExperiment
    {State Action Observation : Set}
    (language : ExperimentLanguage Action)
    (observe : State → Observation)
    (step : Action → State → State)
    (left right : State) : Set₁ where
  constructor admissibleSeparatingExperiment
  field
    actions : List Action
    admissible : Admissible language actions
    separates :
      observe (Future.run step actions left)
      ≡ observe (Future.run step actions right) →
      ⊥

open AdmissibleSeparatingExperiment public

admissibleSeparatingExperimentRefutesLanguageEquivalence :
  ∀ {State Action Observation}
    {language : ExperimentLanguage Action}
    {observe : State → Observation}
    {step : Action → State → State}
    {left right : State} →
  AdmissibleSeparatingExperiment language observe step left right →
  LanguageEquivalent language observe step left right →
  ⊥
admissibleSeparatingExperimentRefutesLanguageEquivalence witness equivalent =
  separates witness
    (equivalent (actions witness) (admissible witness))

RobustLanguageEquivalent :
  ∀ {Context State Action Observation} →
  ExperimentLanguage Action →
  (Context → State → Observation) →
  (Context → Action → State → State) →
  State → State → Set
RobustLanguageEquivalent {Context = Context} language observe step left right =
  (context : Context) →
  LanguageEquivalent language
    (observe context)
    (step context)
    left right

robustLanguageEquivalentAtContext :
  ∀ {Context State Action Observation}
    {language : ExperimentLanguage Action}
    {observe : Context → State → Observation}
    {step : Context → Action → State → State}
    {left right : State} →
  RobustLanguageEquivalent language observe step left right →
  (context : Context) →
  LanguageEquivalent language (observe context) (step context) left right
robustLanguageEquivalentAtContext robust context = robust context

record ExperimentLanguageBoundary : Set where
  constructor experimentLanguageBoundary
  field
    actionAdmissibilityDoesNotImplyTraceAdmissibility : Bool
    equivalenceIsRelativeToDeclaredExperimentLanguage : Bool
    oneAdmissibleSeparatingTraceRefutesEquivalence : Bool
    robustEquivalenceQuantifiesDeclaredContexts : Bool
    boundedLanguageDoesNotEstablishUnboundedCompleteness : Bool

canonicalExperimentLanguageBoundary : ExperimentLanguageBoundary
canonicalExperimentLanguageBoundary =
  experimentLanguageBoundary true true true true true
