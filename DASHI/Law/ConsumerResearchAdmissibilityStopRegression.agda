module DASHI.Law.ConsumerResearchAdmissibilityStopRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.ConsumerResearchAdmissibilityStopExact as Stop

boundary : Stop.ConsumerResearchAdmissibilityStopBoundary
boundary = Stop.canonicalConsumerResearchAdmissibilityStopBoundary

rankingInsideEligibleOnly :
  Stop.rankingOccursOnlyInsideEligibleStratum boundary ≡ true
rankingInsideEligibleOnly =
  Stop.rankingOccursOnlyInsideEligibleStratumIsTrue boundary

paretoRetainsEligibility :
  Stop.paretoSelectionRetainsEligibility boundary ≡ true
paretoRetainsEligibility =
  Stop.paretoSelectionRetainsEligibilityIsTrue boundary

costIsNotTruthRank :
  Stop.lowerResearchCostIsLegalTruthRank boundary ≡ false
costIsNotTruthRank =
  Stop.lowerResearchCostIsLegalTruthRankIsFalse boundary

formalStopRequiresFactorisation :
  Stop.theoremAdequateStopRequiresFactorsThrough boundary ≡ true
formalStopRequiresFactorisation =
  Stop.theoremAdequateStopRequiresFactorsThroughIsTrue boundary

frontierClosureIsNotAdequacy :
  Stop.frontierClosureAloneProvesConsumerAdequacy boundary ≡ false
frontierClosureIsNotAdequacy =
  Stop.frontierClosureAloneProvesConsumerAdequacyIsFalse boundary
