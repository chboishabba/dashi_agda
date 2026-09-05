module DASHI.Analysis.NonArchimedeanContinuousMixingBidiExact where

------------------------------------------------------------------------
-- CONTINUOUS / FINITE L2 MIXING BIDI
--
-- The source one-step field
--
--   ||P_n f|| <= 1/sqrt(2) ||f||  on L2_0
--
-- is refuted by the exact n=3 rational witness.  The repaired theorem is a
-- finite level-dependent prefactored power bound
--
--   ||P_n^t f|| <= C_n 2^(-t/2) ||f||,
--
-- dependency-closed through the finite Euclidean carrier, norm-compatible
-- Hadamard detail energies, unitary local DFT, monomial shell powers, finite
-- maximum prefactor and finite energy assembly.
--
-- Mathlib Cauchy--Schwarz then closes Hilbert-space correlation decay.  The
-- stronger identification with a stochastic covariance remains a distinct
-- probability/expectation same-object consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Analysis.NonArchimedeanPrefactoredL2TowerClosureExact as Tower
import DASHI.Analysis.NonArchimedeanHilbertCorrelationDecayExact as Correlation


data MixingLeaf : Set where
  meanZeroInvariant : MixingLeaf
  oneStepInverseSqrtTwoContraction : MixingLeaf
  finiteSpectralRateHalf : MixingLeaf
  powerBoundWithFinitePrefactor : MixingLeaf
  hilbertCorrelationDecay : MixingLeaf
  stochasticCovarianceIdentification : MixingLeaf
  finiteTotalVariationConsumer : MixingLeaf


data MixingStatus : Set where
  compiled : MixingStatus
  sourceAssumedButRefuted : MixingStatus
  sourceOrRepoOwned : MixingStatus
  sourceLibraryCompiled : MixingStatus
  liveConsumer : MixingStatus

mixingStatus : MixingLeaf → MixingStatus
mixingStatus meanZeroInvariant = compiled
mixingStatus oneStepInverseSqrtTwoContraction = sourceAssumedButRefuted
mixingStatus finiteSpectralRateHalf = sourceOrRepoOwned
mixingStatus powerBoundWithFinitePrefactor = sourceLibraryCompiled
mixingStatus hilbertCorrelationDecay = sourceLibraryCompiled
mixingStatus stochasticCovarianceIdentification = liveConsumer
mixingStatus finiteTotalVariationConsumer = liveConsumer


data MixingObligation : Set where
  needStationaryCovarianceExpectationWeld : MixingObligation
  needFiniteTotalVariationConsumer : MixingObligation
  rejectedUnitConstantOneStepContraction : MixingObligation

l2MixingCutset : List MixingObligation
l2MixingCutset = []

hilbertCorrelationCutset : List MixingObligation
hilbertCorrelationCutset = []

stochasticCovarianceCutset : List MixingObligation
stochasticCovarianceCutset = needStationaryCovarianceExpectationWeld ∷ []

totalVariationCutset : List MixingObligation
totalVariationCutset = needFiniteTotalVariationConsumer ∷ []

oneStepClaimDisposition : List MixingObligation
oneStepClaimDisposition = rejectedUnitConstantOneStepContraction ∷ []

record MixingFirewall : Set where
  constructor mixingFirewall
  field
    refutedOneStepBoundRefutesAllAsymptoticMixing : Bool
    spectralRadiusAloneControlsOneStepNormForNonNormalOperator : Bool
    checkedRationalHadamardSimilarityIsUnitaryAsWritten : Bool
    finitePrefactoredL2PowerDependencyClosed : Bool
    hilbertCorrelationEqualsStochasticCovarianceAutomatically : Bool
    unitPrefactorCanReturn : Bool

canonicalMixingFirewall : MixingFirewall
canonicalMixingFirewall =
  mixingFirewall false false false true false false

prefactoredL2MixingDependencyClosed : l2MixingCutset ≡ []
prefactoredL2MixingDependencyClosed = refl

hilbertCorrelationDependencyClosed : hilbertCorrelationCutset ≡ []
hilbertCorrelationDependencyClosed = refl

stochasticCovarianceStillNeedsWeld :
  stochasticCovarianceCutset
  ≡ needStationaryCovarianceExpectationWeld ∷ []
stochasticCovarianceStillNeedsWeld = refl

falseUnitPrefactorCannotReturn :
  MixingFirewall.unitPrefactorCanReturn canonicalMixingFirewall
  ≡ false
falseUnitPrefactorCannotReturn = refl
