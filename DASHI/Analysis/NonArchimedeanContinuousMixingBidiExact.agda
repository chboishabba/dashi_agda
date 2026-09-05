module DASHI.Analysis.NonArchimedeanContinuousMixingBidiExact where

------------------------------------------------------------------------
-- CONTINUOUS / FINITE L2 MIXING BIDI
--
-- `L2Mixing.lean` defines P_n and L2_0, then stores the one-step mean-zero
-- contraction as a field of `L2MixingAssumptions`.  The source theorem
-- `L2_decay_bound` simply returns that field.
--
-- To obtain a genuine geometric n-step decay theorem from that shape one needs
-- two source-specific receipts:
--
--   1. P_n preserves L2_0;
--   2. the one-step contraction is proved rather than assumed.
--
-- Once those exist, geometric iteration is generic and already has a concrete
-- DASHI precedent in BalabanSelectedBackgroundResidualPowerDecayExact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data MixingLeaf : Set where
  meanZeroInvariant : MixingLeaf
  oneStepMeanZeroContraction : MixingLeaf
  geometricIteration : MixingLeaf
  correlationIdentification : MixingLeaf
  unconditionalExponentialMixing : MixingLeaf


data MixingStatus : Set where
  sourceOwned : MixingStatus
  sourceAssumed : MixingStatus
  live : MixingStatus
  repoReusable : MixingStatus
  downstream : MixingStatus

mixingStatus : MixingLeaf → MixingStatus
mixingStatus meanZeroInvariant = live
mixingStatus oneStepMeanZeroContraction = sourceAssumed
mixingStatus geometricIteration = repoReusable
mixingStatus correlationIdentification = live
mixingStatus unconditionalExponentialMixing = downstream


data MixingObligation : Set where
  needMeanZeroInvariance : MixingObligation
  needUnconditionalOneStepMeanZeroContraction : MixingObligation
  needCorrelationConsumerWeld : MixingObligation

mixingCutset : List MixingObligation
mixingCutset =
  needMeanZeroInvariance ∷
  needUnconditionalOneStepMeanZeroContraction ∷
  needCorrelationConsumerWeld ∷
  []

record MixingFirewall : Set where
  constructor mixingFirewall
  field
    assumptionFieldCountsAsDerivedSpectralBound : Bool
    oneStepBoundCanIterateWithoutInvariantSubspace : Bool
    geometricNormDecayAutomaticallyEqualsCorrelationDecay : Bool
    genericIterationNeedsReproof : Bool

canonicalMixingFirewall : MixingFirewall
canonicalMixingFirewall =
  mixingFirewall false false false false

assumedOneStepBoundNotPromoted :
  MixingFirewall.assumptionFieldCountsAsDerivedSpectralBound
    canonicalMixingFirewall
  ≡ false
assumedOneStepBoundNotPromoted = refl

iterationNeedsInvariantSubspace :
  MixingFirewall.oneStepBoundCanIterateWithoutInvariantSubspace
    canonicalMixingFirewall
  ≡ false
iterationNeedsInvariantSubspace = refl

genericIterationIsReusable :
  MixingFirewall.genericIterationNeedsReproof canonicalMixingFirewall ≡ false
genericIterationIsReusable = refl
