module DASHI.Physics.Closure.NSTriadKNSignedSelfPhaseSelectedPairPaymentExact where

------------------------------------------------------------------------
-- SIGN-ROBUST SELF-PHASE SELECTED-PAIR PAYMENT
--
-- Compose the sign-robust termwise self-phase ED kernel with the existing
-- cardinality-free selected ordered-pair summation.
--
-- A caller supplies the literal selected-pair self contribution and proves,
-- pair by pair on selected entries, that it is below
--
--   D_i E_j + E_i D_j.
--
-- No sign assumption on the Waleffe gap is required.  Once the literal
-- three-slot self forcing is enumerated by such a selector, the whole selected
-- self payment is bounded by 2 E D with no cutoff/cardinality factor.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as Pair

selectedContributionInner :
  ∀ {a} {Mode : Set a} →
  (Mode → Mode → Bool) →
  (Mode → Mode → ℚ) →
  Mode → List Mode → ℚ
selectedContributionInner select contribution left [] = 0ℚ
selectedContributionInner select contribution left (right ∷ rest)
    with select left right
... | true =
  contribution left right
    + selectedContributionInner select contribution left rest
... | false =
  selectedContributionInner select contribution left rest

selectedContributionSum :
  ∀ {a} {Mode : Set a} →
  (Mode → Mode → Bool) →
  (Mode → Mode → ℚ) →
  List Mode → List Mode → ℚ
selectedContributionSum select contribution [] rights = 0ℚ
selectedContributionSum select contribution (left ∷ lefts) rights =
  selectedContributionInner select contribution left rights
    + selectedContributionSum select contribution lefts rights

selectedContributionInnerBelowED :
  ∀ {a} {Mode : Set a}
    (M : Pair.ModalEnergyDissipation Mode)
    (select : Mode → Mode → Bool)
    (contribution : Mode → Mode → ℚ) →
  ((left right : Mode) →
    select left right ≡ true →
    contribution left right ≤ Pair.pairKernel M left right) →
  (left : Mode) (rights : List Mode) →
  selectedContributionInner select contribution left rights
  ≤ Pair.selectedInner M select left rights
selectedContributionInnerBelowED M select contribution termwise left [] =
  ℚP.≤-refl
selectedContributionInnerBelowED M select contribution termwise
    left (right ∷ rest) with select left right
... | true =
  ℚP.+-mono-≤
    (termwise left right refl)
    (selectedContributionInnerBelowED
      M select contribution termwise left rest)
... | false =
  selectedContributionInnerBelowED
    M select contribution termwise left rest

selectedContributionSumBelowED :
  ∀ {a} {Mode : Set a}
    (M : Pair.ModalEnergyDissipation Mode)
    (select : Mode → Mode → Bool)
    (contribution : Mode → Mode → ℚ) →
  ((left right : Mode) →
    select left right ≡ true →
    contribution left right ≤ Pair.pairKernel M left right) →
  (lefts rights : List Mode) →
  selectedContributionSum select contribution lefts rights
  ≤ Pair.selectedOrderedPairSum M select lefts rights
selectedContributionSumBelowED M select contribution termwise [] rights =
  ℚP.≤-refl
selectedContributionSumBelowED M select contribution termwise
    (left ∷ lefts) rights =
  ℚP.+-mono-≤
    (selectedContributionInnerBelowED
      M select contribution termwise left rights)
    (selectedContributionSumBelowED
      M select contribution termwise lefts rights)

signedSelectedSelfPhasePaidByTwoED :
  ∀ {a} {Mode : Set a}
    (M : Pair.ModalEnergyDissipation Mode)
    (select : Mode → Mode → Bool)
    (contribution : Mode → Mode → ℚ) →
  ((left right : Mode) →
    select left right ≡ true →
    contribution left right ≤ Pair.pairKernel M left right) →
  (modes : List Mode) →
  selectedContributionSum select contribution modes modes
  ≤
  Pair.sumEnergy M modes * Pair.sumDissipation M modes
    + Pair.sumEnergy M modes * Pair.sumDissipation M modes
signedSelectedSelfPhasePaidByTwoED M select contribution termwise modes =
  ℚP.≤-trans
    (selectedContributionSumBelowED
      M select contribution termwise modes modes)
    (Pair.selectedPairEnergyDissipationProductBound M select modes)
