module DASHI.Core.MarketMechanismProofExperimentActionCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop
import DASHI.Economics.MarketTransitionGrammarCyberneticsExact as Market
import DASHI.Economics.HistoryIndexedMarketMechanismOODALoopExact as MarketLoop

------------------------------------------------------------------------
-- CROSS-POLLINATION: ACTIVE EPISTEMIC CONTROL <-> MARKET MECHANISM CONTROL
--
-- A market-governance controller may need to think, look, test, or act:
--   think : proof/model analysis of a proposed rule
--   look  : observe market signals/risk under current rules
--   test  : alter a bounded mechanism as an information-producing experiment
--   act   : enact an authorised rule/transition-grammar revision
-- These are kept distinct on the same OODA control spine.
------------------------------------------------------------------------

data MarketControlIntent : Set where
  analyseRule
  observeMarket
  experimentWithMechanism
  reviseRule
  : MarketControlIntent

intentMoveKind : MarketControlIntent → Loop.EpistemicMoveKind
intentMoveKind analyseRule = Loop.thinkMove
intentMoveKind observeMarket = Loop.lookMove
intentMoveKind experimentWithMechanism = Loop.testMove
intentMoveKind reviseRule = Loop.actMove

analyseAndActDiffer :
  intentMoveKind analyseRule ≡ intentMoveKind reviseRule → ⊥
analyseAndActDiffer ()

observeAndExperimentDiffer :
  intentMoveKind observeMarket ≡ intentMoveKind experimentWithMechanism → ⊥
observeAndExperimentDiffer ()

record MarketControlCandidate (fibre : Loop.LiveResidualFibre) : Set₁ where
  constructor marketControlCandidate
  field
    intent : MarketControlIntent
    loopCandidate : Loop.CandidateMove fibre
    moveMatchesIntent :
      Loop.kind loopCandidate ≡ intentMoveKind intent
    marketStateReference : String
    ruleRegimeReference : String
    discoveryResidualReference : String
    riskResidualReference : String

open MarketControlCandidate public

------------------------------------------------------------------------
-- Consumer-relative closure applies here too.  A regulator need not know the
-- complete underlying preference/state configuration if every live hypothesis
-- supports the same action-relevant policy consumer.
------------------------------------------------------------------------

record MarketPolicyConsumerClosure (fibre : Loop.LiveResidualFibre) : Set₁ where
  constructor marketPolicyConsumerClosure
  field
    closure : Loop.ConsumerClosedAt fibre
    policyConsumerReference : String
    unresolvedFineStateReference : String

open MarketPolicyConsumerClosure public

------------------------------------------------------------------------
-- A mechanism experiment can reduce uncertainty without automatically granting
-- authority for permanent policy.  Conversely, authority to revise a rule does
-- not prove that the revision preserves discovery capacity.
------------------------------------------------------------------------

record MechanismExperimentReceipt : Set where
  constructor mechanismExperimentReceipt
  field
    boundedExperiment : MarketLoop.MechanismExperiment
    observedMarketEvidenceReference : String
    residualAfterExperimentReference : String
    permanentRuleAuthorityReference : String

open MechanismExperimentReceipt public

record MarketMechanismCrossPollinationBoundary : Set where
  constructor marketMechanismCrossPollinationBoundary
  field
    successfulExperimentAutomaticallyAuthorisesPermanentRule : Bool
    successfulExperimentAutomaticallyAuthorisesPermanentRuleIsFalse :
      successfulExperimentAutomaticallyAuthorisesPermanentRule ≡ false

    ruleAuthorityProvesDiscoveryPreserved : Bool
    ruleAuthorityProvesDiscoveryPreservedIsFalse :
      ruleAuthorityProvesDiscoveryPreserved ≡ false

    marketSignalEliminatesResidualState : Bool
    marketSignalEliminatesResidualStateIsFalse :
      marketSignalEliminatesResidualState ≡ false

    consumerClosureRequiresCompletePreferenceRecovery : Bool
    consumerClosureRequiresCompletePreferenceRecoveryIsFalse :
      consumerClosureRequiresCompletePreferenceRecovery ≡ false

canonicalMarketMechanismCrossPollinationBoundary :
  MarketMechanismCrossPollinationBoundary
canonicalMarketMechanismCrossPollinationBoundary =
  marketMechanismCrossPollinationBoundary
    false refl
    false refl
    false refl
    false refl
