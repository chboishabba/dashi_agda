{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedGibbsWickTimeCorrectionBidiExact where

------------------------------------------------------------------------
-- ACTUAL FINITE WILSON/GIBBS MEASURE: EUCLIDEAN DIAGONAL INSERTIONS
-- VERSUS LORENTZIAN TIMELIKE ENERGY
--
-- This module uses the existing *one selected finite measure* plus its
-- literal Wilson/Gibbs N/Z/DN/DZ derivatives to extract c00,c11,c22,c33.
-- If a physically established analytic continuation sends the Euclidean
-- temporal connected numerator c00 to Lorentzian energy rho=-c00, then
--
--   Euclidean sum E = c00+c11+c22+c33
--   Lorentzian trace Theta = E
--   Lorentzian active A = -c00+c11+c22+c33 = E - 2*c00.
--
-- If analytic continuation instead sends rho=+c00, the Euclidean sum is A,
-- and the Lorentzian trace is E-2*c00. This module proves both candidate
-- algebraic maps WITHOUT pretending the Wick choice is already settled.
--
-- NB: both sums are CONNECTED NUMERATORS, not normalized expectation
-- values. The same Z>0 and metric stress normalization must be supplied
-- before using either as renormalized Lorentzian T_mu_nu.
--
-- Original owners: classical SU2 Wilson variation, finite Haar measure,
-- physical connected insertion quotient rule. DASHI: sign-convention
-- firewall and two-way Euclidean/Lorentzian timelike reconstruction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; -_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTraceInsertionReductionExact as Trace
import DASHI.Physics.Foundations.CMP119GibbsDiagonalTraceCancellationExact as Cancel
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Laws
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

module _
  {Configuration : Set}
  {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
  (selected : Wilson.ClassicalWilsonSelectedInsertion Configuration)
  (laws : Laws.RationalFiniteMeasureIntegrationLaws measure)
  where

  selectedGibbsC00 : ℚ
  selectedGibbsC00 =
    Cancel.c00 (Trace.gibbsData selected laws)
      Trace.diagonalDirections laws
      (Trace.actionTraceZero selected laws)

  selectedGibbsC11 : ℚ
  selectedGibbsC11 =
    Cancel.c11 (Trace.gibbsData selected laws)
      Trace.diagonalDirections laws
      (Trace.actionTraceZero selected laws)

  selectedGibbsC22 : ℚ
  selectedGibbsC22 =
    Cancel.c22 (Trace.gibbsData selected laws)
      Trace.diagonalDirections laws
      (Trace.actionTraceZero selected laws)

  selectedGibbsC33 : ℚ
  selectedGibbsC33 =
    Cancel.c33 (Trace.gibbsData selected laws)
      Trace.diagonalDirections laws
      (Trace.actionTraceZero selected laws)

  selectedEuclideanDiagonalSum : ℚ
  selectedEuclideanDiagonalSum =
    Trace.activeConnectedNumerator selected laws

  negativeTemporalWickActive : ℚ
  negativeTemporalWickActive =
    - selectedGibbsC00 + selectedGibbsC11
      + selectedGibbsC22 + selectedGibbsC33

  negativeTemporalWickTrace : ℚ
  negativeTemporalWickTrace =
    selectedEuclideanDiagonalSum

  positiveTemporalWickActive : ℚ
  positiveTemporalWickActive =
    selectedEuclideanDiagonalSum

  negativeTemporalWickEnergy : ℚ
  negativeTemporalWickEnergy = - selectedGibbsC00

  positiveTemporalWickEnergy : ℚ
  positiveTemporalWickEnergy = selectedGibbsC00

  positiveTemporalWickTrace : ℚ
  positiveTemporalWickTrace =
    - selectedGibbsC00 + selectedGibbsC11
      + selectedGibbsC22 + selectedGibbsC33

  -- The missing timelike term is EXACTLY a twice-temporal correction,
  -- not a re-labelling of the Euclidean insertion sum.
  negativeWickActiveDiffersFromEuclideanSum :
    negativeTemporalWickActive
      ≡ selectedEuclideanDiagonalSum
        - ((1ℚ + 1ℚ) * selectedGibbsC00)
  negativeWickActiveDiffersFromEuclideanSum =
    Ring.solve-∀
      selectedGibbsC00 selectedGibbsC11
      selectedGibbsC22 selectedGibbsC33

  positiveWickTraceDiffersFromEuclideanSum :
    positiveTemporalWickTrace
      ≡ selectedEuclideanDiagonalSum
        - ((1ℚ + 1ℚ) * selectedGibbsC00)
  positiveWickTraceDiffersFromEuclideanSum =
    Ring.solve-∀
      selectedGibbsC00 selectedGibbsC11
      selectedGibbsC22 selectedGibbsC33

  negativeWickActiveIsTracePlusTimelikeEnergy :
    negativeTemporalWickActive
    ≡ negativeTemporalWickTrace
      + ((1ℚ + 1ℚ) * negativeTemporalWickEnergy)
  negativeWickActiveIsTracePlusTimelikeEnergy =
    Ring.solve-∀
      selectedGibbsC00 selectedGibbsC11
      selectedGibbsC22 selectedGibbsC33

  positiveWickActiveIsTracePlusTimelikeEnergy :
    positiveTemporalWickActive
    ≡ positiveTemporalWickTrace
      + ((1ℚ + 1ℚ) * positiveTemporalWickEnergy)
  positiveWickActiveIsTracePlusTimelikeEnergy =
    Ring.solve-∀
      selectedGibbsC00 selectedGibbsC11
      selectedGibbsC22 selectedGibbsC33

  -- If the selected Lorentzian convention is established, these two
  -- identities reconstruct the full trace + 2*T00 source from the SAME
  -- four finite-metric derivative numerators. At no point is the T00
  -- sign chosen to make the active sum negative.

  -- SHARP SIGN TEST for the actual four selected connected numerators:
  -- under rho=-c00 Wick identification, outward local Ricci contribution
  -- requires Euclidean sum < 2*c00, not simply Euclidean sum < 0.
  negativeWickActiveImpliesTimelikeThreshold :
    negativeTemporalWickActive < 0ℚ →
    selectedEuclideanDiagonalSum
      < (1ℚ + 1ℚ) * selectedGibbsC00
  negativeWickActiveImpliesTimelikeThreshold negative =
    let
      changed :
        selectedEuclideanDiagonalSum
          - ((1ℚ + 1ℚ) * selectedGibbsC00) < 0ℚ
      changed =
        subst (_< 0ℚ)
          (negativeWickActiveDiffersFromEuclideanSum)
          negative
    in
    subst₂ _<_
      (Ring.solve-∀
        selectedEuclideanDiagonalSum selectedGibbsC00)
      (Ring.solve-∀ selectedGibbsC00)
      (ℚP.+-monoʳ-<
        ((1ℚ + 1ℚ) * selectedGibbsC00) changed)

  timelikeThresholdImpliesNegativeWickActive :
    selectedEuclideanDiagonalSum
      < (1ℚ + 1ℚ) * selectedGibbsC00 →
    negativeTemporalWickActive < 0ℚ
  timelikeThresholdImpliesNegativeWickActive threshold =
    subst (_< 0ℚ)
      (sym negativeWickActiveDiffersFromEuclideanSum)
      (subst₂ _<_
        (Ring.solve-∀
          selectedEuclideanDiagonalSum selectedGibbsC00)
        (Ring.solve-∀ selectedGibbsC00)
        (ℚP.+-monoʳ-<
          (- ((1ℚ + 1ℚ) * selectedGibbsC00)) threshold))

-- Pure algebraic counterfixture illustrating why negative Euclidean sum
-- is not enough under a negative temporal Wick continuation. No claim
-- that this fixture is the selected Wilson measure.
counterexampleEuclideanSum : ℚ
counterexampleEuclideanSum = - (1ℚ + 1ℚ)

counterexampleLorentzianActive : ℚ
counterexampleLorentzianActive =
  - (- (1ℚ + 1ℚ))

counterexampleSignReversal :
  counterexampleLorentzianActive ≡ 1ℚ + 1ℚ
counterexampleSignReversal = Ring.solve-∀
