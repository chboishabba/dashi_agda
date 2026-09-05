module DASHI.Analysis.NonArchimedeanContinuousTransferClaimStrengthExact where

------------------------------------------------------------------------
-- CONTINUOUS TRANSFER CLAIM-STRENGTH MATRIX
--
-- Source audit of ContinuousTransfer.lean + L2Mixing.lean versus the stronger
-- README/monograph prose.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)


data ContinuousClaim : Set where
  transferOperatorDefined : ContinuousClaim
  markovOperatorDefined : ContinuousClaim
  constantEigenvalueTwo : ContinuousClaim
  normalizedConstantEigenvalueOne : ContinuousClaim
  gibbsMarkovEquivalence : ContinuousClaim
  branchInvariantImpliesGibbs : ContinuousClaim
  haarIsConformalGibbs : ContinuousClaim
  haarUniqueConformalGibbs : ContinuousClaim
  twistedCircleRadiusSequence : ContinuousClaim
  twistedCircleRadiusConvergesOne : ContinuousClaim
  fullTransferRadiusSqrtTwo : ContinuousClaim
  essentialSpectralRadiusOne : ContinuousClaim
  meanZeroL2OneStepBound : ContinuousClaim
  unconditionalExponentialMixing : ContinuousClaim
  correlationDecayRate : ContinuousClaim


data ClaimStrength : Set where
  sourceOwned : ClaimStrength
  sourceOwnedConditional : ClaimStrength
  sourceNotLocated : ClaimStrength
  proseOnlyOrOverstated : ClaimStrength

claimStrength : ContinuousClaim → ClaimStrength
claimStrength transferOperatorDefined = sourceOwned
claimStrength markovOperatorDefined = sourceOwned
claimStrength constantEigenvalueTwo = sourceOwned
claimStrength normalizedConstantEigenvalueOne = sourceOwned
claimStrength gibbsMarkovEquivalence = sourceOwned
claimStrength branchInvariantImpliesGibbs = sourceOwned
claimStrength haarIsConformalGibbs = sourceOwnedConditional
claimStrength haarUniqueConformalGibbs = sourceNotLocated
claimStrength twistedCircleRadiusSequence = sourceOwned
claimStrength twistedCircleRadiusConvergesOne = sourceOwned
claimStrength fullTransferRadiusSqrtTwo = proseOnlyOrOverstated
claimStrength essentialSpectralRadiusOne = sourceNotLocated
claimStrength meanZeroL2OneStepBound = sourceOwnedConditional
claimStrength unconditionalExponentialMixing = sourceNotLocated
claimStrength correlationDecayRate = sourceNotLocated

record ContinuousClaimFirewall : Set where
  constructor continuousClaimFirewall
  field
    invarianceImpliesUniqueness : Bool
    oneStepConditionalBoundImpliesUnconditionalMixing : Bool
    namedSpectralRadiusSequenceIsFullOperatorRadius : Bool
    proseCompletedLabelImpliesLeanTheorem : Bool

canonicalContinuousClaimFirewall : ContinuousClaimFirewall
canonicalContinuousClaimFirewall =
  continuousClaimFirewall false false false false

gibbsInvarianceDoesNotProveUniqueness :
  ContinuousClaimFirewall.invarianceImpliesUniqueness
    canonicalContinuousClaimFirewall
  ≡ false
gibbsInvarianceDoesNotProveUniqueness = refl

conditionalBoundDoesNotAutoPromoteMixing :
  ContinuousClaimFirewall.oneStepConditionalBoundImpliesUnconditionalMixing
    canonicalContinuousClaimFirewall
  ≡ false
conditionalBoundDoesNotAutoPromoteMixing = refl

fullOperatorRadiusCannotReuseCircleName :
  ContinuousClaimFirewall.namedSpectralRadiusSequenceIsFullOperatorRadius
    canonicalContinuousClaimFirewall
  ≡ false
fullOperatorRadiusCannotReuseCircleName = refl
