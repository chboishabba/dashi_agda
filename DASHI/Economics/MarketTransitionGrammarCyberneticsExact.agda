module DASHI.Economics.MarketTransitionGrammarCyberneticsExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- MARKET AS TRANSITION PRODUCER / SENSOR INSIDE A CYBERNETIC ECONOMY
--
-- The market is neither identified with the whole coordination system nor
-- treated as its opposite.  A rule regime determines which candidate
-- transitions may be expressed.  Behaviour under that regime emits signals;
-- regulators may then revise the admissible transition grammar.
------------------------------------------------------------------------

record MarketCyberneticSurface : Set₁ where
  constructor marketCyberneticSurface
  field
    State : Set
    Actor : Set
    Instrument : Set
    Transition : Set
    RuleRegime : Set
    Signal : Set
    RiskObservation : Set

    proposes : Actor → State → Transition → Set
    usesInstrument : Transition → Instrument → Set
    admittedBy : RuleRegime → State → Transition → Set
    emitsSignal : RuleRegime → State → Transition → Signal → Set
    observesRisk : RuleRegime → State → RiskObservation → Set

    reference : String

open MarketCyberneticSurface public

------------------------------------------------------------------------
-- A market rule regime controls the grammar of lawful transitions without
-- thereby fixing every individual transition or market price.
------------------------------------------------------------------------

record TransitionGrammarChange (surface : MarketCyberneticSurface) : Set₁ where
  constructor transitionGrammarChange
  field
    before after : RuleRegime surface
    transition : Transition surface
    admittedBefore :
      (state : State surface) → admittedBy surface before state transition → Set
    changeReference : String

open TransitionGrammarChange public

record InstrumentedMarketExperiment (surface : MarketCyberneticSurface) : Set₁ where
  constructor instrumentedMarketExperiment
  field
    regime : RuleRegime surface
    initialState : State surface
    observedSignal : Signal surface
    observedRisk : RiskObservation surface
    signalReference : String
    riskReference : String

open InstrumentedMarketExperiment public

------------------------------------------------------------------------
-- Discovery capacity is kept distinct from coordination/control authority.
-- Tightening the transition grammar may reduce risk while also discarding
-- information-producing experimentation; neither implication is automatic.
------------------------------------------------------------------------

data DiscoveryDirection : Set where
  discoveryReduced discoveryPreserved discoveryExpanded discoveryUnknown
  : DiscoveryDirection

data RiskDirection : Set where
  riskReduced riskPreserved riskExpanded riskUnknown : RiskDirection

record RuleRevisionAssessment : Set where
  constructor ruleRevisionAssessment
  field
    discoveryEffect : DiscoveryDirection
    riskEffect : RiskDirection
    assessmentReference : String

open RuleRevisionAssessment public

------------------------------------------------------------------------
-- Distinct signal roles.  A price/market signal may mix physical demand,
-- hedging, leverage, speculation, and liquidity effects; the surface does not
-- equate any one component with the whole signal.
------------------------------------------------------------------------

data SignalRole : Set where
  physicalDemandSignal
  hedgingSignal
  leverageSignal
  speculativeSignal
  liquiditySignal
  administrativeSignal
  : SignalRole

record TypedMarketSignal (surface : MarketCyberneticSurface) : Set₁ where
  constructor typedMarketSignal
  field
    signal : Signal surface
    role : SignalRole
    provenance : String

open TypedMarketSignal public

------------------------------------------------------------------------
-- Transition producers coexist.  Jurisdiction over a transition class is an
-- explicit receipt, not inferred from the existence of a producer.
------------------------------------------------------------------------

data ProducerKind : Set where
  marketProducer firmProducer governmentProducer aiProducer humanProducer
  : ProducerKind

record TransitionProducerJurisdiction
    (surface : MarketCyberneticSurface) : Set₁ where
  constructor transitionProducerJurisdiction
  field
    producer : ProducerKind
    transition : Transition surface
    jurisdictionReference : String

open TransitionProducerJurisdiction public

------------------------------------------------------------------------
-- Boundary / anti-collapse laws.
------------------------------------------------------------------------

record MarketTransitionGrammarBoundary : Set where
  constructor marketTransitionGrammarBoundary
  field
    marketIsWholeCoordinationSystem : Bool
    marketIsWholeCoordinationSystemIsFalse :
      marketIsWholeCoordinationSystem ≡ false

    changingRulesSetsEveryPrice : Bool
    changingRulesSetsEveryPriceIsFalse : changingRulesSetsEveryPrice ≡ false

    admittedTransitionImpliesObservedPreference : Bool
    admittedTransitionImpliesObservedPreferenceIsFalse :
      admittedTransitionImpliesObservedPreference ≡ false

    tighterGrammarNecessarilyImprovesSignalQuality : Bool
    tighterGrammarNecessarilyImprovesSignalQualityIsFalse :
      tighterGrammarNecessarilyImprovesSignalQuality ≡ false

    lowerRiskNecessarilyPreservesDiscovery : Bool
    lowerRiskNecessarilyPreservesDiscoveryIsFalse :
      lowerRiskNecessarilyPreservesDiscovery ≡ false

    priceObservationRevealsPrivateInformationCompletely : Bool
    priceObservationRevealsPrivateInformationCompletelyIsFalse :
      priceObservationRevealsPrivateInformationCompletely ≡ false

canonicalMarketTransitionGrammarBoundary : MarketTransitionGrammarBoundary
canonicalMarketTransitionGrammarBoundary =
  marketTransitionGrammarBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
