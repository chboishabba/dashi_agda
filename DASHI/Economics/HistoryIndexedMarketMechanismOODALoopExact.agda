module DASHI.Economics.HistoryIndexedMarketMechanismOODALoopExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.MarketTransitionGrammarCyberneticsExact as Market

------------------------------------------------------------------------
-- HISTORY-INDEXED MARKET-MECHANISM OODA LOOP
--
-- Rule_t -> behaviour/signal_t -> observed risk/discovery -> rule_{t+1}.
-- A regulator can therefore redesign the experimental envelope within which
-- decentralized actors search, without being identified with the actors or
-- with every transition they subsequently choose.
------------------------------------------------------------------------

record HistoryIndexedMarketControlSurface : Set₁ where
  constructor historyIndexedMarketControlSurface
  field
    History : Set
    Time : Set
    Regime : Set
    Behaviour : Set
    Signal : Set
    Risk : Set
    DiscoveryState : Set

    regimeAt : History → Time → Regime
    behaviourAt : History → Time → Behaviour
    signalAt : History → Time → Signal
    riskAt : History → Time → Risk
    discoveryAt : History → Time → DiscoveryState

    surfaceReference : String

open HistoryIndexedMarketControlSurface public

record MarketMechanismOODAStep
    (surface : HistoryIndexedMarketControlSurface)
    (history : History surface)
    (before after : Time surface) : Set₁ where
  constructor marketMechanismOODAStep
  field
    observedBehaviour : Behaviour surface
    observedBehaviourExact :
      observedBehaviour ≡ behaviourAt surface history before

    observedSignal : Signal surface
    observedSignalExact : observedSignal ≡ signalAt surface history before

    observedRisk : Risk surface
    observedRiskExact : observedRisk ≡ riskAt surface history before

    observedDiscovery : DiscoveryState surface
    observedDiscoveryExact :
      observedDiscovery ≡ discoveryAt surface history before

    revisedRegime : Regime surface
    revisedRegimeExact : revisedRegime ≡ regimeAt surface history after

    revisionReference : String

open MarketMechanismOODAStep public

------------------------------------------------------------------------
-- Model/policy revision is separated from merely observing a changed market.
------------------------------------------------------------------------

record RuleRevisionAuthority
    (surface : HistoryIndexedMarketControlSurface)
    (history : History surface)
    (before after : Time surface) : Set₁ where
  constructor ruleRevisionAuthority
  field
    sourceRegime : Regime surface
    targetRegime : Regime surface
    sourceExact : sourceRegime ≡ regimeAt surface history before
    targetExact : targetRegime ≡ regimeAt surface history after
    authorityReference : String
    provenanceReference : String

open RuleRevisionAuthority public

------------------------------------------------------------------------
-- Market rules can themselves be used as experimental interventions.  The
-- resulting behaviour is evidence about actors under that regime, not direct
-- access to counterfactual true preferences under every other regime.
------------------------------------------------------------------------

record MechanismExperiment : Set where
  constructor mechanismExperiment
  field
    interventionReference : String
    observedOutcomeReference : String
    counterfactualResidualReference : String

open MechanismExperiment public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record HistoryIndexedMarketMechanismBoundary : Set where
  constructor historyIndexedMarketMechanismBoundary
  field
    observedBehaviourIsLatentPreference : Bool
    observedBehaviourIsLatentPreferenceIsFalse :
      observedBehaviourIsLatentPreference ≡ false

    regulatorChoosesEveryActorTransition : Bool
    regulatorChoosesEveryActorTransitionIsFalse :
      regulatorChoosesEveryActorTransition ≡ false

    changedRiskForcesOneUniqueRuleRevision : Bool
    changedRiskForcesOneUniqueRuleRevisionIsFalse :
      changedRiskForcesOneUniqueRuleRevision ≡ false

    regimeChangeMayBeTreatedAsExperiment : Bool
    regimeChangeMayBeTreatedAsExperimentIsTrue :
      regimeChangeMayBeTreatedAsExperiment ≡ true

    marketFeedbackMayReviseTransitionGrammar : Bool
    marketFeedbackMayReviseTransitionGrammarIsTrue :
      marketFeedbackMayReviseTransitionGrammar ≡ true

canonicalHistoryIndexedMarketMechanismBoundary :
  HistoryIndexedMarketMechanismBoundary
canonicalHistoryIndexedMarketMechanismBoundary =
  historyIndexedMarketMechanismBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
