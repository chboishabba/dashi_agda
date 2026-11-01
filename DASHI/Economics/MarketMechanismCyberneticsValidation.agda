module DASHI.Economics.MarketMechanismCyberneticsValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Economics.MarketTransitionGrammarCyberneticsExact as Market
import DASHI.Economics.FinancialPhysicalBackingMarketControlExact as Backing
import DASHI.Economics.ChinaRetailGoldMarketTopology2026Exact as Gold
import DASHI.Economics.HistoryIndexedMarketMechanismOODALoopExact as OODA
import DASHI.Core.MarketMechanismProofExperimentActionCrossPollinationExact as Cross

marketIsNotWholeSystem :
  Market.marketIsWholeCoordinationSystem
    Market.canonicalMarketTransitionGrammarBoundary ≡ false
marketIsNotWholeSystem = refl

priceIsNotFixedByRuleRevision :
  Market.changingRulesSetsEveryPrice
    Market.canonicalMarketTransitionGrammarBoundary ≡ false
priceIsNotFixedByRuleRevision = refl

discoveryIsNotFree :
  Market.lowerRiskNecessarilyPreservesDiscovery
    Market.canonicalMarketTransitionGrammarBoundary ≡ false
discoveryIsNotFree = refl

paperRestrictionIsNotPhysicalBan :
  Backing.paperRestrictionImpliesPhysicalBan
    Backing.canonicalFinancialPhysicalBackingBoundary ≡ false
paperRestrictionIsNotPhysicalBan = refl

goldFixtureIsSelective :
  Gold.fixtureSupportsSelectiveChannelRetrenchment
    Gold.canonicalChinaRetailGoldTopologyBoundary ≡ true
goldFixtureIsSelective = refl

goldFixtureIsNotBlanketBan :
  Gold.fixtureProvesBlanketNationalGoldBan
    Gold.canonicalChinaRetailGoldTopologyBoundary ≡ false
goldFixtureIsNotBlanketBan = refl

rulesMayBeExperiments :
  OODA.regimeChangeMayBeTreatedAsExperiment
    OODA.canonicalHistoryIndexedMarketMechanismBoundary ≡ true
rulesMayBeExperiments = refl

experimentDoesNotAuthorisePermanentRule :
  Cross.successfulExperimentAutomaticallyAuthorisesPermanentRule
    Cross.canonicalMarketMechanismCrossPollinationBoundary ≡ false
experimentDoesNotAuthorisePermanentRule = refl

policyClosureDoesNotRequirePreferenceRecovery :
  Cross.consumerClosureRequiresCompletePreferenceRecovery
    Cross.canonicalMarketMechanismCrossPollinationBoundary ≡ false
policyClosureDoesNotRequirePreferenceRecovery = refl
