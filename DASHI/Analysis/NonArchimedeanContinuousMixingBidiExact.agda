module DASHI.Analysis.NonArchimedeanContinuousMixingBidiExact where

------------------------------------------------------------------------
-- CONTINUOUS / FINITE L2 MIXING BIDI
--
-- `L2Mixing.lean` stores the one-step mean-zero contraction as a field of
-- `L2MixingAssumptions`; `L2_decay_bound` simply returns that field.
--
-- Mean-zero invariance is no longer a live leaf: the finite Collatz branches
-- x -> 3x and x -> 3x-1 are permutations because the source already constructs
-- inv3 and proves three_mul_inv3 = 1.  Finite sum reindexing gives mass
-- preservation, and the generic zero-fibre compiler gives P_n(L2_0) subset L2_0.
--
-- Hence the only live analytic producer for geometric L2 decay is the actual
-- derivation of the one-step 1/sqrt(2) contraction.  Geometric iteration is
-- repo-reusable.  Correlation decay additionally needs a consumer weld.
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
  compiled : MixingStatus
  sourceAssumed : MixingStatus
  live : MixingStatus
  repoReusable : MixingStatus
  downstream : MixingStatus

mixingStatus : MixingLeaf → MixingStatus
mixingStatus meanZeroInvariant = compiled
mixingStatus oneStepMeanZeroContraction = sourceAssumed
mixingStatus geometricIteration = repoReusable
mixingStatus correlationIdentification = live
mixingStatus unconditionalExponentialMixing = downstream


data MixingObligation : Set where
  needUnconditionalOneStepMeanZeroContraction : MixingObligation
  needCorrelationConsumerWeld : MixingObligation

l2MixingCutset : List MixingObligation
l2MixingCutset =
  needUnconditionalOneStepMeanZeroContraction ∷ []

correlationDecayCutset : List MixingObligation
correlationDecayCutset =
  needUnconditionalOneStepMeanZeroContraction ∷
  needCorrelationConsumerWeld ∷ []

record MixingFirewall : Set where
  constructor mixingFirewall
  field
    assumptionFieldCountsAsDerivedSpectralBound : Bool
    meanZeroInvarianceStillNeedsSearch : Bool
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

meanZeroSearchNowPruned :
  MixingFirewall.meanZeroInvarianceStillNeedsSearch canonicalMixingFirewall ≡ false
meanZeroSearchNowPruned = refl

genericIterationIsReusable :
  MixingFirewall.genericIterationNeedsReproof canonicalMixingFirewall ≡ false
genericIterationIsReusable = refl
