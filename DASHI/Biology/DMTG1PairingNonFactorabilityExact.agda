module DASHI.Biology.DMTG1PairingNonFactorabilityExact where

-- Source-specific finite observer collision for original EEG G1 *pairing*.
-- Formalisation/research direction: Johl Brown; AI-assisted code: OpenAI
-- ChatGPT (26 Oct 2026). Arithmetic is ordinary finite algebra, not a
-- novel theorem attributed to the user or AI.
--
-- Primary experimental authors: Niedernhuber, Suay, Lenggenhager,
-- Müller, Scheidegger, Dornbierer, Aicher (2026),
-- DOI 10.1177/02698811261481062. Their data are NOT represented here.
-- The original export/source pairing remains unverified from raw records.
--
-- Statistical/method donors: Billingsley; Kullback; von Wegner et al.;
-- Tait and Zhang's +microstate (2022), DOI 10.1016/j.neuroimage.2022.119346.
-- Previous finite no-factorisation OWNER:
-- DASHI.Core.IntersectionalNonFactorability. No duplicate generic theorem.
-- Idea and source-boundary inspiration from separate PRs #1266 and #1268;
-- those unmerged files are NOT imported.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _-_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF

-- Synthetic G1 by-person values, NOT collected EEG:
--   DMT:     10,20,30
--   placebo:  8,18,28
-- Same treatment marginals in either world; only the person-to-row
-- assignment in the second column changes. Placebo reversal swaps 8 and 28.
data RowAssignment : Set where
  matchedOriginalOrder : RowAssignment
  sameMarginalsReversedOrder : RowAssignment

data ThreeValues (A : Set) : Set where
  threeValues : A → A → A → ThreeValues A

record UnkeyedConditionMarginals : Set where
  constructor conditionMarginals
  field
    sortedDMT : ThreeValues Nat
    sortedPlacebo : ThreeValues Nat

-- A literal source-independent *value* observer, not a verbal assertion
-- that the two assignments have the same marginals.
unkeyedObserver : RowAssignment → UnkeyedConditionMarginals
unkeyedObserver matchedOriginalOrder =
  conditionMarginals (threeValues 10 20 30) (threeValues 8 18 28)
unkeyedObserver sameMarginalsReversedOrder =
  conditionMarginals (threeValues 10 20 30) (threeValues 8 18 28)

-- Unlike source G1, these are elementary synthetic product sums.
pairedCrossMoment : RowAssignment → Nat
pairedCrossMoment matchedOriginalOrder =
  (10 * 8) + ((20 * 18) + (30 * 28))
pairedCrossMoment sameMarginalsReversedOrder =
  (10 * 28) + ((20 * 18) + (30 * 8))

matchedCrossMoment : pairedCrossMoment matchedOriginalOrder ≡ 1280
matchedCrossMoment = refl

reversedCrossMoment : pairedCrossMoment sameMarginalsReversedOrder ≡ 880
reversedCrossMoment = refl

momentsDiffer :
  pairedCrossMoment matchedOriginalOrder ≡
  pairedCrossMoment sameMarginalsReversedOrder → ⊥
momentsDiffer ()

-- Actual pairwise centered sum-of-squares, not an uninterpreted label.
-- All assignments have mean(DMT-placebo)=2. The quantity
--   sum_i [ (DMT_i - placebo_i) - 2 ]^2
-- equals 0 in the matched world and 800 in the reversed world.
-- For three observations the SAMPLE variance is this / (3-1),
-- so the corresponding variances are 0 and 400.
-- Nat subtraction is truncated; adding its two orientations yields
-- the nonnegative absolute difference of the two nonnegative arguments.
absDifference : Nat → Nat → Nat
absDifference a b = (a - b) + (b - a)

square : Nat → Nat
square n = n * n

centeredSquaredDifference : Nat → Nat → Nat
centeredSquaredDifference dmt placebo =
  square (absDifference dmt (placebo + 2))

pairedCenteredSquares : RowAssignment → Nat
pairedCenteredSquares matchedOriginalOrder =
  centeredSquaredDifference 10 8 +
  (centeredSquaredDifference 20 18 +
   centeredSquaredDifference 30 28)
pairedCenteredSquares sameMarginalsReversedOrder =
  centeredSquaredDifference 10 28 +
  (centeredSquaredDifference 20 18 +
   centeredSquaredDifference 30 8)

matchedCenteredSquares : pairedCenteredSquares matchedOriginalOrder ≡ 0
matchedCenteredSquares = refl

reversedCenteredSquares : pairedCenteredSquares sameMarginalsReversedOrder ≡ 800
reversedCenteredSquares = refl

pairedVariationDiffers :
  pairedCenteredSquares matchedOriginalOrder ≡
  pairedCenteredSquares sameMarginalsReversedOrder → ⊥
pairedVariationDiffers ()

-- Exact reuse of the pre-existing generic non-factorability certificate.
pairingCollision : NF.NonFactorabilityWitness
  unkeyedObserver pairedCenteredSquares
pairingCollision =
  NF.nonFactorabilityWitness
    matchedOriginalOrder sameMarginalsReversedOrder
    refl pairedVariationDiffers

-- ANY downstream statistic of just the unkeyed marginal vectors
-- is incapable of recovering the assigned-pair variance in both worlds.
-- It must refine its observation with a source-verified person/arm join.
noPairedVarianceFromUnkeyedMarginals :
  NF.FactorsThrough unkeyedObserver pairedCenteredSquares → ⊥
noPairedVarianceFromUnkeyedMarginals =
  NF.witnessRulesOutEveryFlatFactorisation pairingCollision

noRechartCanRepairUnkeyedPairing :
  {Recharted : Set} →
  (rechart : UnkeyedConditionMarginals → Recharted) →
  NF.FactorsThrough
    (λ pairing → rechart (unkeyedObserver pairing))
    pairedCenteredSquares → ⊥
noRechartCanRepairUnkeyedPairing rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart pairingCollision

-- Exact scope: this is a constructed counterexample, not a finding that
-- Niedernhuber et al. misaligned participants. Their MATLAB export appears
-- to remove missing rows jointly; the code alone does not independently
-- attest the participant identity of those positional rows.
