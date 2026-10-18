module DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact where

------------------------------------------------------------------------
-- FINITE RG WEIGHTED LAW -> LITERAL FINITE PROBABILITY EXPECTATION
--
-- FiniteRGReopeningStep already computes
--
--   E[O] = sum_x fineWeight(x) O(x)
--
-- on an explicit finite state list, but the reopening ABI does not itself say
-- that fineWeight is nonnegative or normalized.  Those two facts are exactly
-- what is needed before the weighted functional may be used as a probability
-- expectation.
--
-- This module adds only that least-privilege probability refinement and proves
-- the finite Markov/sublevel inequality directly on the literal rational sum.
-- No abstract expectation-is-integral predicate is introduced:
-- finiteProbabilityIntegral IS the existing RG expectation definition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRationalOrderCoreExact as Order
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact as R283
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Preferred
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram

record FiniteRGProbabilityLaw {Fine Coarse : Set}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse) : Set₁ where
  field
    fineWeightNonnegative : ∀ fine → 0ℚ ≤ Reopen.fineWeight step fine
    fineWeightNormalized :
      Sums.sumRational (Reopen.fineStates step) (Reopen.fineWeight step)
      ≡ 1ℚ

open FiniteRGProbabilityLaw public

finiteProbabilityIntegral :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  Reopen.Observable Fine → ℚ
finiteProbabilityIntegral = Reopen.fineExpectation

finiteProbabilityIntegralIsRGExpectation :
  ∀ {Fine Coarse}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    observable →
  finiteProbabilityIntegral step observable
  ≡ Reopen.fineExpectation step observable
finiteProbabilityIntegralIsRGExpectation step observable = refl

finiteProbabilityMass :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  ℚ
finiteProbabilityMass step =
  Sums.sumRational (Reopen.fineStates step) (Reopen.fineWeight step)

finiteProbabilityMassIsOne :
  ∀ {Fine Coarse}
    {step : Reopen.FiniteRGReopeningStep Fine Coarse} →
  FiniteRGProbabilityLaw step →
  finiteProbabilityMass step ≡ 1ℚ
finiteProbabilityMassIsOne = fineWeightNormalized

------------------------------------------------------------------------
-- Literal event/sublevel mass on the same finite state list.
------------------------------------------------------------------------

selectedWeight :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  (Fine → Bool) → Fine → ℚ
selectedWeight step event fine with event fine
... | true = Reopen.fineWeight step fine
... | false = 0ℚ

eventMass :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  (Fine → Bool) → ℚ
eventMass step event =
  Sums.sumRational (Reopen.fineStates step) (selectedWeight step event)

selectedThresholdTerm :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  (Fine → Bool) → ℚ → Fine → ℚ
selectedThresholdTerm step outside threshold fine =
  threshold * selectedWeight step outside fine

weightedObservableTerm :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  Reopen.Observable Fine → Fine → ℚ
weightedObservableTerm step observable fine =
  Reopen.fineWeight step fine * observable fine

selectedThresholdPointwiseBelowObservable :
  ∀ {Fine Coarse}
    {step : Reopen.FiniteRGReopeningStep Fine Coarse}
    (law : FiniteRGProbabilityLaw step)
    (outside : Fine → Bool)
    (threshold : ℚ)
    (observable : Reopen.Observable Fine) →
  (∀ fine → 0ℚ ≤ observable fine) →
  (∀ fine → outside fine ≡ true → threshold ≤ observable fine) →
  ∀ fine →
  selectedThresholdTerm step outside threshold fine
  ≤ weightedObservableTerm step observable fine
selectedThresholdPointwiseBelowObservable {step = step}
  law outside threshold observable observableNonnegative outsideLower fine
  with outside fine
... | true =
  let
    instance
      weightNN : NonNegative (Reopen.fineWeight step fine)
      weightNN = nonNegative (fineWeightNonnegative law fine)

    scaled :
      Reopen.fineWeight step fine * threshold
      ≤ Reopen.fineWeight step fine * observable fine
    scaled =
      ℚP.*-monoˡ-≤-nonNeg
        (Reopen.fineWeight step fine)
        (outsideLower fine refl)
  in
  subst
    (λ left →
      left ≤ Reopen.fineWeight step fine * observable fine)
    (ℚP.*-comm (Reopen.fineWeight step fine) threshold)
    scaled
... | false =
  let
    instance
      weightNN : NonNegative (Reopen.fineWeight step fine)
      weightNN = nonNegative (fineWeightNonnegative law fine)

      observableNN : NonNegative (observable fine)
      observableNN = nonNegative (observableNonnegative fine)

    productNN :
      0ℚ ≤ Reopen.fineWeight step fine * observable fine
    productNN = ℚP.nonNegative⁻¹ _
  in
  subst
    (λ left →
      left ≤ Reopen.fineWeight step fine * observable fine)
    (sym (ℚP.*-zeroʳ threshold))
    productNN

finiteMarkovSublevel :
  ∀ {Fine Coarse}
    {step : Reopen.FiniteRGReopeningStep Fine Coarse} →
  FiniteRGProbabilityLaw step →
  (outside : Fine → Bool) →
  (threshold : ℚ) →
  (observable : Reopen.Observable Fine) →
  (∀ fine → 0ℚ ≤ observable fine) →
  (∀ fine → outside fine ≡ true → threshold ≤ observable fine) →
  threshold * eventMass step outside
  ≤ finiteProbabilityIntegral step observable
finiteMarkovSublevel {step = step} law outside threshold observable
  observableNonnegative outsideLower =
  let
    summed :
      Sums.sumRational (Reopen.fineStates step)
        (selectedThresholdTerm step outside threshold)
      ≤
      Sums.sumRational (Reopen.fineStates step)
        (weightedObservableTerm step observable)
    summed =
      Order.sumRationalMonotone
        (Reopen.fineStates step)
        (selectedThresholdTerm step outside threshold)
        (weightedObservableTerm step observable)
        (selectedThresholdPointwiseBelowObservable
          law outside threshold observable
          observableNonnegative outsideLower)

    leftFactor :
      Sums.sumRational (Reopen.fineStates step)
        (selectedThresholdTerm step outside threshold)
      ≡ threshold * eventMass step outside
    leftFactor =
      Sums.sumRationalScale
        threshold
        (Reopen.fineStates step)
        (selectedWeight step outside)
  in
  subst
    (λ left → left ≤ finiteProbabilityIntegral step observable)
    leftFactor
    summed

------------------------------------------------------------------------
-- Same-object transport into the preferred selected T5 finite expectation.
------------------------------------------------------------------------

record SelectedT5FiniteProbabilityPresentation
    (Measure Fine Coarse : Set)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    presentation :
      R283.FiniteVolumeReopeningPresentation Measure Fine Coarse thermodynamic

    probabilityAt : ∀ cutoff →
      FiniteRGProbabilityLaw (R283.stepAt presentation cutoff)

open SelectedT5FiniteProbabilityPresentation public

selectedT5ProbabilityIntegral :
  ∀ {Measure Fine Coarse}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ} →
  SelectedT5FiniteProbabilityPresentation Measure Fine Coarse thermodynamic →
  Nat → Reopen.Observable Fine → ℚ
selectedT5ProbabilityIntegral semantics cutoff observable =
  finiteProbabilityIntegral
    (R283.stepAt (presentation semantics) cutoff)
    observable

selectedT5ExpectationIsProbabilityIntegral :
  ∀ {Measure Fine Coarse}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    (semantics :
      SelectedT5FiniteProbabilityPresentation
        Measure Fine Coarse thermodynamic)
    cutoff observable →
  Gram.expectation (T5.operations thermodynamic)
    (Preferred.selectedFiniteVolumeSequence thermodynamic cutoff)
    observable
  ≡ selectedT5ProbabilityIntegral semantics cutoff observable
selectedT5ExpectationIsProbabilityIntegral semantics cutoff observable =
  R283.finiteVolumeExpectationIsReopeningExpectation
    (presentation semantics) cutoff observable

finiteRGProbabilitySemanticsLevel : ProofLevel
finiteRGProbabilitySemanticsLevel = machineChecked

finiteMarkovSublevelLevel : ProofLevel
finiteMarkovSublevelLevel = machineChecked

selectedT5ExpectationIntegralTransportLevel : ProofLevel
selectedT5ExpectationIntegralTransportLevel = machineChecked

selectedFiniteRGProbabilityLawLevel : ProofLevel
selectedFiniteRGProbabilityLawLevel = conditional

round283SelectedFinitePresentationLevel : ProofLevel
round283SelectedFinitePresentationLevel = conditional
