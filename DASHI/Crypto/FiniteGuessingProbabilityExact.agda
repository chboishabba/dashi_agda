module DASHI.Crypto.FiniteGuessingProbabilityExact where

------------------------------------------------------------------------
-- FINITE GUESSING-PROBABILITY / MIN-ENTROPY PRECURSOR
--
-- Cryptographic uncertainty is not identified with candidate cardinality or
-- search cost.  This finite layer records exact count ratios before importing
-- logarithms or a probability library.  The intended future interpretation is
-- conditional guessing probability / min-entropy.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

record GuessingExperiment : Set where
  constructor guessingExperiment
  field
    totalMass bestLabelMass : Nat

open GuessingExperiment public

-- A refinement can improve guessing probability without proving cheap search.
record GuessingRefinement : Set where
  constructor guessingRefinement
  field
    before after : GuessingExperiment
    candidateCountBefore candidateCountAfter : Nat
    recoveryCostBefore recoveryCostAfter : Nat

open GuessingRefinement public

balancedTwoWay : GuessingExperiment
balancedTwoWay = guessingExperiment 2 1

identifiedOneWay : GuessingExperiment
identifiedOneWay = guessingExperiment 1 1

finiteGuessingImprovesTwoToOne : GuessingRefinement
finiteGuessingImprovesTwoToOne =
  guessingRefinement balancedTwoWay identifiedOneWay 2 1 13 10

bestMassBefore : bestLabelMass (before finiteGuessingImprovesTwoToOne) ≡ 1
bestMassBefore = refl

bestMassAfter : bestLabelMass (after finiteGuessingImprovesTwoToOne) ≡ 1
bestMassAfter = refl

denominatorShrinks :
  totalMass (before finiteGuessingImprovesTwoToOne) ≡ 2
  × totalMass (after finiteGuessingImprovesTwoToOne) ≡ 1
denominatorShrinks = refl , refl

------------------------------------------------------------------------
-- Counterexample to identifying statistical and computational gain: the same
-- 2->1 statistical identification can coexist with worse declared recovery
-- cost under another algorithm/observation architecture.
------------------------------------------------------------------------

statisticallyBetterComputationallyWorse : GuessingRefinement
statisticallyBetterComputationallyWorse =
  guessingRefinement balancedTwoWay identifiedOneWay 2 1 2 11

statisticalGainDoesNotImplySearchGain :
  candidateCountAfter statisticallyBetterComputationallyWorse ≡ 1
  × recoveryCostAfter statisticallyBetterComputationallyWorse ≡ 11
statisticalGainDoesNotImplySearchGain = refl , refl
