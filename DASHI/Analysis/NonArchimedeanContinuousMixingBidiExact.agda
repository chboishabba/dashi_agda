module DASHI.Analysis.NonArchimedeanContinuousMixingBidiExact where

------------------------------------------------------------------------
-- CONTINUOUS / FINITE L2 MIXING BIDI
--
-- The source one-step field
--
--   ||P_n f|| <= 1/sqrt(2) ||f||  on L2_0
--
-- is not merely unproved: the exact n=3 rational witness in
-- NonArchimedeanL2MixingN3CounterexampleExact refutes its squared necessary
-- form.  Mean-zero invariance itself compiles from existing source inverse-of-3
-- arithmetic and finite sum reindexing.
--
-- This does NOT refute asymptotic mixing with a prefactor C_n > 1.  For a
-- non-normal finite operator, transient norm amplification may coexist with
-- spectral-rate decay of powers.  The viable target is therefore a power bound
--
--   ||P_n^t|L2_0|| <= C_n * 2^(-t/2),
--
-- produced from the now-owned finite spectral/monomial decomposition plus a
-- conditioning/power-control theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data MixingLeaf : Set where
  meanZeroInvariant : MixingLeaf
  oneStepInverseSqrtTwoContraction : MixingLeaf
  finiteSpectralRateHalf : MixingLeaf
  powerBoundWithPrefactor : MixingLeaf
  correlationIdentification : MixingLeaf
  unconditionalExponentialMixing : MixingLeaf


data MixingStatus : Set where
  compiled : MixingStatus
  sourceAssumedButRefuted : MixingStatus
  sourceOrRepoOwned : MixingStatus
  live : MixingStatus
  downstream : MixingStatus

mixingStatus : MixingLeaf → MixingStatus
mixingStatus meanZeroInvariant = compiled
mixingStatus oneStepInverseSqrtTwoContraction = sourceAssumedButRefuted
mixingStatus finiteSpectralRateHalf = sourceOrRepoOwned
mixingStatus powerBoundWithPrefactor = live
mixingStatus correlationIdentification = live
mixingStatus unconditionalExponentialMixing = downstream


data MixingObligation : Set where
  needFinitePowerBoundWithPrefactor : MixingObligation
  needCorrelationConsumerWeld : MixingObligation
  rejectedUnitConstantOneStepContraction : MixingObligation

l2MixingCutset : List MixingObligation
l2MixingCutset = needFinitePowerBoundWithPrefactor ∷ []

correlationDecayCutset : List MixingObligation
correlationDecayCutset =
  needFinitePowerBoundWithPrefactor ∷ needCorrelationConsumerWeld ∷ []

oneStepClaimDisposition : List MixingObligation
oneStepClaimDisposition = rejectedUnitConstantOneStepContraction ∷ []

record MixingFirewall : Set where
  constructor mixingFirewall
  field
    refutedOneStepBoundRefutesAllAsymptoticMixing : Bool
    spectralRadiusAloneControlsOneStepNormForNonNormalOperator : Bool
    spectralRateAloneSuppliesPowerPrefactor : Bool
    geometricNormDecayAutomaticallyEqualsCorrelationDecay : Bool
    meanZeroInvarianceStillNeedsSearch : Bool

canonicalMixingFirewall : MixingFirewall
canonicalMixingFirewall =
  mixingFirewall false false false false false

oneStepNoGoDoesNotKillPrefactoredMixing :
  MixingFirewall.refutedOneStepBoundRefutesAllAsymptoticMixing
    canonicalMixingFirewall
  ≡ false
oneStepNoGoDoesNotKillPrefactoredMixing = refl

spectralRadiusDoesNotControlOneStepNormHere :
  MixingFirewall.spectralRadiusAloneControlsOneStepNormForNonNormalOperator
    canonicalMixingFirewall
  ≡ false
spectralRadiusDoesNotControlOneStepNormHere = refl

powerPrefactorStillNeedsReceipt :
  mixingStatus powerBoundWithPrefactor ≡ live
powerPrefactorStillNeedsReceipt = refl
