module DASHI.Physics.Closure.NSTriadKNHHBadGainBelowDefectProfileRound51Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 50 required equality between the literal normalized HH-bad gain
-- coefficient and the directional-defect profile.  The mature owner consumes
-- only an upper bound.  Round 51 therefore weakens the same-object seam to
--
--   2^q g_q <= C_q <= M,
--
-- which is sufficient to build the same selected-threshold owner with eta 2M.
-- This keeps exact equality only at the earlier literal Fourier/rawGain seam
-- and permits the directional defect to control production without being
-- definitionally identical to it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHHBadSummableForcingRound50Exact as Sum

record GainBelowDefectProfileBridge
    (effectiveViscosity : ℚ)
    (summableInput : Sum.BorderlineSummableForcing) : Set where
  field
    selectedThreshold : Threshold.PositiveThreshold
    density : Nat → ℚ
    densityNonnegative : ∀ shell → 0ℚ ≤ density shell
    cells : ∀ shell →
      List (Gain.RestrictedGainDensityCell
        effectiveViscosity (density shell) shell)

    normalizedDensityBelowDefectProfile : ∀ shell →
      Factor.scaleFreeDensityCoefficient (density shell) shell
      ≤ Sum.profile summableInput shell

open GainBelowDefectProfileBridge public

profileCeilingFromSummableForcing : Sum.BorderlineSummableForcing → ℚ
profileCeilingFromSummableForcing input =
  Sum.profile input zero + Sum.totalForcingBudget input

profileCeilingNonnegative :
  (input : Sum.BorderlineSummableForcing) →
  0ℚ ≤ Sum.profile input zero →
  0ℚ ≤ profileCeilingFromSummableForcing input
profileCeilingNonnegative input baseNN =
  ℚP.+-mono-≤ baseNN (Sum.totalForcingBudgetNonnegative input)

gainDominationToSelectedProfile :
  ∀ {effectiveViscosity summableInput} →
  (bridge : GainBelowDefectProfileBridge
    effectiveViscosity summableInput) →
  Sum.PrefixSummable summableInput →
  0ℚ ≤ Sum.profile summableInput zero →
  Selected.SelectedThresholdHHBadNormalizedProfile effectiveViscosity
gainDominationToSelectedProfile {summableInput = input}
    bridge prefix baseNN = record
  { selectedThreshold = selectedThreshold bridge
  ; density = density bridge
  ; densityNonnegative = densityNonnegative bridge
  ; cells = cells bridge
  ; selectedProfileCeiling = profileCeilingFromSummableForcing input
  ; selectedProfileCeilingNonnegative = profileCeilingNonnegative input baseNN
  ; normalizedCoefficientBelowSelectedCeiling = λ shell →
      ℚP.≤-trans
        (normalizedDensityBelowDefectProfile bridge shell)
        (Sum.profileBelowBasePlusBudget input prefix shell)
  }

gainDefectEqualityRequiredByOwnerConsumer : Bool
gainDefectEqualityRequiredByOwnerConsumer = false

gainDefectDominationSufficesForOwnerConsumer : Bool
gainDefectDominationSufficesForOwnerConsumer = true

gainDefectEqualityRequiredByOwnerConsumerIsFalse :
  gainDefectEqualityRequiredByOwnerConsumer ≡ false
gainDefectEqualityRequiredByOwnerConsumerIsFalse = refl

gainDefectDominationSufficesForOwnerConsumerIsTrue :
  gainDefectDominationSufficesForOwnerConsumer ≡ true
gainDefectDominationSufficesForOwnerConsumerIsTrue = refl
