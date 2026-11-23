module DASHI.Culture.AmyEskridgeTransparentPsiOriginalCodePriorSensitivityExact where

-- SOURCE-EXACT original transparent Psi authors' analysis script:
-- https://github.com/kekecsz/Transparent_psi_RR_materials/blob/master/TPP_Statistical_analysis_script_FINAL.R
-- SHA: 4ec79f47bf11f73a6094dac1f3860a65f26e7a5d.
-- Lines 163–203: 18 trials/person, 37836 initial stopping point,
-- BF01 >=25, null .5, 1% SESOI, 0.6% ROPE.
-- Lines 176–179 explicitly use y_prior=828, N_prior=1560.
-- ORIGINAL received Bem EXP1.xlsx source SHA
-- feadd752a26f997327f12921eb916d9154b9907e27205aca64b9a22a0ea2df45
-- instead supports source reconstructed 826/1560 pooled guesses.
--
-- This module establishes exact integer source discrepancies,
-- prior-identity and the complete permitted integer hit-count set
-- consistent with reported 49.89% rounded to TWO decimals and N=37836.
-- Bayes-factor beta integrals are independently evaluated in Python/SciPy
-- and are NOT claimed as native Agda proofs of the beta distribution.
--
-- IMPORTANT: A prior sensitivity test does not reconstruct original
-- GLMM, sequential stopping or all 4 prespecified tests.
-- Replication raw 11 file GitHub directory is located, but very large
-- CSV data could not be transferred to current local Python checkout.
-- Raw data are still NOT 'replayed'.

open import Agda.Builtin.Nat using (Nat; _+_; _*_; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)
import DASHI.Culture.AmyEskridgeBemExp1OriginalWorkbookReplayExact as Bem
import DASHI.Culture.AmyEskridgeVideoTemporalForecastAndPsiMaxCutExact as Psi

leq : Nat → Nat → Bool
leq zero _ = true
leq (suc _) zero = false
leq (suc a) (suc b) = leq a b

notBool : Bool → Bool
notBool true = false
notBool false = true

andBool : Bool → Bool → Bool
andBool true b = b
andBool false _ = false

lt : Nat → Nat → Bool
lt a b = notBool (leq b a)

originalTransparentPsiPriorSuccesses : Nat
originalTransparentPsiPriorSuccesses = 828

originalTransparentPsiPriorTrials : Nat
originalTransparentPsiPriorTrials = 1560

actualBemWorkbookSuccesses : Nat
actualBemWorkbookSuccesses = Bem.originalHitCount

originalPriorVsDirectWorkbookDifference :
  actualBemWorkbookSuccesses + 2 ≡ originalTransparentPsiPriorSuccesses
originalPriorVsDirectWorkbookDifference = refl

priorTrialsStillMatchWorkbook :
  originalTransparentPsiPriorTrials ≡ Bem.originalEroticTrials
priorTrialsStillMatchWorkbook = refl

firstPreregisteredStopTrials : Nat
firstPreregisteredStopTrials = 37836

-- Reporting 49.89 percent to nearest 0.01 percent permits
-- success fractions in [0.49885,0.49895) at this fixed sample size.
compatibleReportedTwoDecimalRate : Nat → Bool
compatibleReportedTwoDecimalRate successes =
  andBool (leq (49885 * firstPreregisteredStopTrials) (successes * 100000))
          (lt (successes * 100000) (49895 * firstPreregisteredStopTrials))

roundedCount18875 : compatibleReportedTwoDecimalRate 18875 ≡ true
roundedCount18875 = refl

roundedCount18876 : compatibleReportedTwoDecimalRate 18876 ≡ true
roundedCount18876 = refl

roundedCount18877 : compatibleReportedTwoDecimalRate 18877 ≡ true
roundedCount18877 = refl

roundedCount18878 : compatibleReportedTwoDecimalRate 18878 ≡ true
roundedCount18878 = refl

roundedCount18874Excluded :
  compatibleReportedTwoDecimalRate 18874 ≡ false
roundedCount18874Excluded = refl

roundedCount18879Excluded :
  compatibleReportedTwoDecimalRate 18879 ≡ false
roundedCount18879Excluded = refl

-- Original experimental design explicitly records two sensation-seeking
-- answers SS_Q_item_1/SS_Q_item_2; first is REVERSE scored (6-x).
-- These are NOT source-identical to Bem's original 2011 variable.
record MeasuredModeratorProvenance : Set where
  constructor measured-moderator
  field
    originalItemCount : Nat
    firstItemReverseScored : Bool
    originalBemScoreIdentical : Bool
    originalMeasureMappingValidated : Bool
    sourceResearchScriptVersionMatched : Bool

transparentPsiSensationSeeking : MeasuredModeratorProvenance
transparentPsiSensationSeeking =
  measured-moderator 2 true false false true

data ExactSameStimulusScaleClaim : Set where
data AggregateNullDemonstratesNoHighSeekerEffect : Set where
data RoundedStatisticDeterminesExactReplicatedHits : Set where

noUncalibratedScaleEquivalence : ExactSameStimulusScaleClaim → ⊥
noUncalibratedScaleEquivalence ()
noAggregateAsSubgroupRefutation :
  AggregateNullDemonstratesNoHighSeekerEffect → ⊥
noAggregateAsSubgroupRefutation ()
noRoundedToUniqueHitCount :
  RoundedStatisticDeterminesExactReplicatedHits → ⊥
noRoundedToUniqueHitCount ()

-- Original separately reported endpoint remains a SOURCE value,
-- not a reconstructable GLMM from only a scalar percentage.
publishedReplicationRateIs4899BasisPoints :
  Psi.transparentPsi2023ReportedRate ≡ 4989
publishedReplicationRateIs4899BasisPoints = refl
