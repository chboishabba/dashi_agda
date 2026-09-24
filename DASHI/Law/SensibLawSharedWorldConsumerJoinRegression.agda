module DASHI.Law.SensibLawSharedWorldConsumerJoinRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.SensibLawSharedWorldConsumerJoinExact as Join

boundary : Join.SharedWorldConsumerJoinBoundary
boundary = Join.canonicalSharedWorldConsumerJoinBoundary

consumerRelative :
  Join.joinIsConsumerRelativeDependency boundary ≡ true
consumerRelative =
  Join.joinIsConsumerRelativeDependencyIsTrue boundary

proposalNotEnough :
  Join.proposalBasisAloneEstablishesJoin boundary ≡ false
proposalNotEnough =
  Join.proposalBasisAloneEstablishesJoinIsFalse boundary

reviewedReuseAllowed :
  Join.reviewedCoordinateMayBeReusedAcrossConsumers boundary ≡ true
reviewedReuseAllowed =
  Join.reviewedCoordinateMayBeReusedAcrossConsumersIsTrue boundary

reuseDoesNotCollapse :
  Join.reuseCollapsesDistinctLegalConsumers boundary ≡ false
reuseDoesNotCollapse =
  Join.reuseCollapsesDistinctLegalConsumersIsFalse boundary

alreadyPaidQuotients :
  Join.alreadyPaidCoordinateMayQuotientResearch boundary ≡ true
alreadyPaidQuotients =
  Join.alreadyPaidCoordinateMayQuotientResearchIsTrue boundary

reuseCreatesNoTruth :
  Join.sharedReuseCreatesClaimTruth boundary ≡ false
reuseCreatesNoTruth =
  Join.sharedReuseCreatesClaimTruthIsFalse boundary
