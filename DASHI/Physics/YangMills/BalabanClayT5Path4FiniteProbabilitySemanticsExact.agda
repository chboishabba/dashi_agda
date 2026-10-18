module DASHI.Physics.YangMills.BalabanClayT5Path4FiniteProbabilitySemanticsExact where

------------------------------------------------------------------------
-- PATH4 OBSERVABLE SEMANTICS ON THE SAME FINITE PROBABILITY LAW
--
-- The preferred T5 producer chooses its diagonal measure definitionally from
-- the finite-volume family.  Round283 identifies expectation on that exact
-- finite measure with the finite-RG weighted expectation.  The probability
-- refinement proves those finite RG weights form a normalized nonnegative law.
--
-- This module adds the final same-object semantic weld for Path4: on the
-- finite state carrier, observableValue is ordinary function evaluation.
-- Therefore the selected T5 expectation of the literal Path4 gauge-energy
-- observable is the literal weighted finite probability integral of the same
-- pointwise values.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Probability
import DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact as R283
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Preferred
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Path4

record Path4PreferredFiniteProbabilitySemantics
    (Measure Fine Coarse : Set)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ)
    (preferred :
      Preferred.PreferredDiagonalExpectationProducerInputs
        Measure (Reopen.Observable Fine) ℚ thermodynamic)
    (probability :
      Probability.SelectedT5FiniteProbabilityPresentation
        Measure Fine Coarse thermodynamic)
    (realization :
      Path4.Path4GaugeEnergyObservableRealization
        Measure (Reopen.Observable Fine) Fine
        (Preferred.compilePreferredDiagonalExpectationProducer preferred)) : Set₁ where
  field
    observableValueIsApplication :
      ∀ observable fine →
      Path4.observableValue realization observable fine ≡ observable fine

open Path4PreferredFiniteProbabilitySemantics public

path4FiniteProbabilityIntegral :
  ∀ {Measure Fine Coarse thermodynamic preferred probability realization} →
  Path4PreferredFiniteProbabilitySemantics
    Measure Fine Coarse thermodynamic preferred probability realization →
  (cutoff : Nat) → ℚ
path4FiniteProbabilityIntegral
  {probability = probability} {realization = realization} semantics cutoff =
  let
    step = R283.stepAt
      (Probability.presentation probability) cutoff
  in
  Sums.sumRational
    (Reopen.fineStates step)
    (λ fine →
      Reopen.fineWeight step fine
      * Path4.observableValue realization
          (Path4.path4GaugeEnergyObservable realization)
          fine)

rgPath4ObservableIntegralAgreement :
  ∀ {Measure Fine Coarse thermodynamic preferred probability realization}
    (semantics :
      Path4PreferredFiniteProbabilitySemantics
        Measure Fine Coarse thermodynamic preferred probability realization)
    cutoff →
  Probability.selectedT5ProbabilityIntegral probability cutoff
    (Path4.path4GaugeEnergyObservable realization)
  ≡ path4FiniteProbabilityIntegral semantics cutoff
rgPath4ObservableIntegralAgreement
  {probability = probability} {realization = realization}
  semantics cutoff =
  let
    step = R283.stepAt
      (Probability.presentation probability) cutoff
  in
  Sums.sumRationalCong
    (Reopen.fineStates step)
    (λ fine →
      Reopen.fineWeight step fine
      * Path4.path4GaugeEnergyObservable realization fine)
    (λ fine →
      Reopen.fineWeight step fine
      * Path4.observableValue realization
          (Path4.path4GaugeEnergyObservable realization)
          fine)
    (λ fine →
      cong
        (Reopen.fineWeight step fine *_)
        (sym
          (observableValueIsApplication semantics
            (Path4.path4GaugeEnergyObservable realization)
            fine)))

selectedPath4ExpectationIsFiniteProbabilityIntegral :
  ∀ {Measure Fine Coarse thermodynamic preferred probability realization}
    (semantics :
      Path4PreferredFiniteProbabilitySemantics
        Measure Fine Coarse thermodynamic preferred probability realization)
    cutoff →
  Gram.expectation (T5.operations thermodynamic)
    (T5.diagonalMeasure
      (Preferred.compilePreferredDiagonalExpectationProducer preferred)
      cutoff)
    (Path4.path4GaugeEnergyObservable realization)
  ≡ path4FiniteProbabilityIntegral semantics cutoff
selectedPath4ExpectationIsFiniteProbabilityIntegral
  {thermodynamic = thermodynamic}
  {preferred = preferred}
  {probability = probability}
  {realization = realization}
  semantics cutoff =
  trans
    (Preferred.preferredDiagonalExpectationSameObject
      preferred cutoff (Path4.path4GaugeEnergyObservable realization))
    (trans
      (Probability.selectedT5ExpectationIsProbabilityIntegral
        probability cutoff
        (Path4.path4GaugeEnergyObservable realization))
      (rgPath4ObservableIntegralAgreement semantics cutoff))

path4FiniteProbabilitySemanticsCompilerLevel : ProofLevel
path4FiniteProbabilitySemanticsCompilerLevel = machineChecked

path4SelectedExpectationIntegralWeldLevel : ProofLevel
path4SelectedExpectationIntegralWeldLevel = machineChecked

-- Remaining physical/source semantics are now localized:
-- (1) Round283 must identify the selected finite T5 expectation with the
--     exact finite-RG law;
-- (2) the selected finite RG weights must be a normalized nonnegative law;
-- (3) the literal Path4 observable realization must be supplied on that exact
--     finite state carrier.
path4FiniteProbabilityPresentationLevel : ProofLevel
path4FiniteProbabilityPresentationLevel = conditional

path4ObservableEvaluationRealizationLevel : ProofLevel
path4ObservableEvaluationRealizationLevel = conditional
