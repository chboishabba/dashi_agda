module DASHI.Law.ConsumerDirectedLegalFollowAdequacyRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.ConsumerDirectedLegalFollowAdequacyExact as Consumer

boundary : Consumer.ConsumerDirectedLegalFollowAdequacyBoundary
boundary =
  Consumer.canonicalConsumerDirectedLegalFollowAdequacyBoundary

runtimeReceiptIsNotFormalProof :
  Consumer.runtimeCoverageReceiptIsFormalFactorsThroughProof boundary ≡ false
runtimeReceiptIsNotFormalProof =
  Consumer.runtimeCoverageReceiptIsFormalFactorsThroughProofIsFalse boundary

missingAxisIsNotAdequate :
  Consumer.missingRequiredAxisMayBeTreatedAsAdequate boundary ≡ false
missingAxisIsNotAdequate =
  Consumer.missingRequiredAxisMayBeTreatedAsAdequateIsFalse boundary

nonFactorabilityRoutesResearch :
  Consumer.nonFactorabilityMayRouteTypedResearchDemand boundary ≡ true
nonFactorabilityRoutesResearch =
  Consumer.nonFactorabilityMayRouteTypedResearchDemandIsTrue boundary

refinementMayRepair :
  Consumer.addingMissingAxisMayRepairAdequacy boundary ≡ true
refinementMayRepair =
  Consumer.addingMissingAxisMayRepairAdequacyIsTrue boundary

closedAxisMayTerminate :
  Consumer.explicitlyClosedMissingAxisMayTerminateUnresolved boundary ≡ true
closedAxisMayTerminate =
  Consumer.explicitlyClosedMissingAxisMayTerminateUnresolvedIsTrue boundary

unresolvedCreatesNoTruth :
  Consumer.unresolvedTerminationCreatesClaimTruth boundary ≡ false
unresolvedCreatesNoTruth =
  Consumer.unresolvedTerminationCreatesClaimTruthIsFalse boundary

adequacyCreatesNoAuthority :
  Consumer.consumerAdequacyCreatesLegalAuthority boundary ≡ false
adequacyCreatesNoAuthority =
  Consumer.consumerAdequacyCreatesLegalAuthorityIsFalse boundary
