module DASHI.Physics.YangMills.BalabanFiniteRGCovarianceSummableDecayExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- R. Kotecky and D. Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- P. K. Mitter, "The Exact Renormalization Group",
-- arXiv:math-ph/0505008. No DOI recorded for the cited encyclopedia preprint.
--
-- DASHI CONTRIBUTION
--
-- The preceding module proves the exact finite covariance telescope.  Here we
-- do the next mathematical step rather than adding another receipt: a
-- proof-bearing scale-by-scale exponential envelope is summed by induction.
-- If, with one common nonnegative decay factor e(x,y),
--
--     |Cov_N|       <= a_N e,
--     |FibreCov_j|  <= a_j e,
--
-- then
--
--     |Cov_0| <= (a_N + sum_j a_j) e.
--
-- Thus all distance dependence factors out before the scale sum.  The global
-- mass-gap lane is reduced exactly to producing physical one-step amplitudes
-- whose scale sum is uniformly bounded in volume and cutoff.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRGMultiscaleCovarianceTelescopingExact as Telescope

------------------------------------------------------------------------
-- A scale-aligned amplitude certificate for an exact covariance chain.
------------------------------------------------------------------------

data SummableDecayBudget :
    ∀ {fine : ℚ} →
    Telescope.ExactCovarianceChain fine →
    ℚ → ℚ → Set where
  terminalBudget :
    ∀ value decay amplitude →
    0ℚ ≤ decay →
    ∣ value ∣ ≤ amplitude * decay →
    SummableDecayBudget (Telescope.terminal value) decay amplitude

  prependBudget :
    ∀ {fine coarse : ℚ}
      {remainder : ℚ}
      {exact : fine ≡ coarse + remainder}
      {tail : Telescope.ExactCovarianceChain coarse}
      {decay tailAmplitude localAmplitude} →
    SummableDecayBudget tail decay tailAmplitude →
    ∣ remainder ∣ ≤ localAmplitude * decay →
    0ℚ ≤ localAmplitude →
    SummableDecayBudget
      (Telescope.prepend remainder exact tail)
      decay (tailAmplitude + localAmplitude)

summableDecayBudgetUpper :
  ∀ {fine decay amplitude}
    {chain : Telescope.ExactCovarianceChain fine} →
  SummableDecayBudget chain decay amplitude →
  ∣ fine ∣ ≤ amplitude * decay
summableDecayBudgetUpper
    (terminalBudget value decay amplitude decayNonnegative terminalBound) =
  terminalBound
summableDecayBudgetUpper
    {decay = decay}
    (prependBudget {fine} {coarse} {remainder} {exact} {tail}
      {tailAmplitude = tailAmplitude} {localAmplitude = localAmplitude}
      tailBudget remainderBound localNonnegative) =
  let
    oneStep : ∣ fine ∣ ≤ ∣ coarse ∣ + ∣ remainder ∣
    oneStep =
      subst
        (λ lower → lower ≤ ∣ coarse ∣ + ∣ remainder ∣)
        (sym (congAbs exact))
        (ℚP.∣p+q∣≤∣p∣+∣q∣ coarse remainder)
      where
        congAbs : ∀ {x y : ℚ} → x ≡ y → ∣ x ∣ ≡ ∣ y ∣
        congAbs refl = refl

    tailBound : ∣ coarse ∣ ≤ tailAmplitude * decay
    tailBound = summableDecayBudgetUpper tailBudget

    summed :
      ∣ coarse ∣ + ∣ remainder ∣
      ≤ tailAmplitude * decay + localAmplitude * decay
    summed = ℚP.+-mono-≤ tailBound remainderBound

    factorExact :
      tailAmplitude * decay + localAmplitude * decay
      ≡ (tailAmplitude + localAmplitude) * decay
    factorExact = ℚRing.solve []
  in
  ℚP.≤-trans oneStep
    (subst
      (λ upper →
        tailAmplitude * decay + localAmplitude * decay ≤ upper)
      factorExact
      ℚP.≤-refl)

------------------------------------------------------------------------
-- Separate total-amplitude cap.  This is the exact finite precursor of the
-- desired uniform statement sum_j a_j < infinity.
------------------------------------------------------------------------

summableDecayBudgetWithAmplitudeCap :
  ∀ {fine decay amplitude cap}
    {chain : Telescope.ExactCovarianceChain fine} →
  SummableDecayBudget chain decay amplitude →
  amplitude ≤ cap →
  0ℚ ≤ decay →
  ∣ fine ∣ ≤ cap * decay
summableDecayBudgetWithAmplitudeCap
    {decay = decay} budget amplitudeCap decayNonnegative =
  let
    base = summableDecayBudgetUpper budget
    instance
      decayNN : NonNegative decay
      decayNN = ℚ.nonNegative decayNonnegative
  in
  ℚP.≤-trans base (ℚP.*-monoʳ-≤-nonNeg decay amplitudeCap)

finiteRGCovarianceSummableDecayLevel : ProofLevel
finiteRGCovarianceSummableDecayLevel = machineChecked

finiteRGCovarianceUniformAmplitudeCapLevel : ProofLevel
finiteRGCovarianceUniformAmplitudeCapLevel = machineChecked

-- This is now the sole physical producer needed by this finite theorem:
-- construct the one-step bounds and a cutoff/volume-independent cap on their
-- accumulated amplitudes.
ym4ConditionalFibreCovarianceContractsOneStepLevel : ProofLevel
ym4ConditionalFibreCovarianceContractsOneStepLevel = conditional
