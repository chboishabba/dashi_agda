{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyMarkovBridgeExact where

------------------------------------------------------------------------
-- LITERAL PATH4 ENERGY SEMANTICS -> SELECTED MOMENT COMPACT CONTAINMENT
--
-- This preferred route is intentionally indexed by one exact expectationData.
-- It does not try to inhabit the older over-general Markov authority quantified
-- over arbitrary operations/measure sequences. The existing typed moment bound
-- on the selected diagonal producer is consumed directly.
--
-- IMPORTANT: T5.PhysicalOSOperations leaves `expectation` abstract. Therefore
-- the Markov/sublevel implication below is NOT generic probability theory until
-- the selected expectation has been identified with the probability integral
-- of the same pointwise observable semantics. We keep that implication as an
-- explicit physical/representation seam rather than hiding it in a standard
-- authority label.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate using
  (configuredPathCoercivityConstant)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact using
  (physicalUnweightedNormSq)
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5MomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Realization

Path4PointwiseNonnegative :
  ∀ {Measure Observable Configuration}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ} →
  Realization.Path4GaugeEnergyObservableRealization
    Measure Observable Configuration expectationData →
  Observable → Set
Path4PointwiseNonnegative realization observable =
  ∀ configuration →
    0ℚ ≤ Realization.observableValue realization observable configuration

Path4PointwiseCoercive :
  ∀ {Measure Observable Configuration}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ} →
  Realization.Path4GaugeEnergyObservableRealization
    Measure Observable Configuration expectationData →
  Observable → Set
Path4PointwiseCoercive realization observable =
  ∀ configuration →
    configuredPathCoercivityConstant
      * physicalUnweightedNormSq
          (Realization.physicalTangentCoordinate realization configuration)
    ≤ Realization.observableValue realization observable configuration

record Path4SelectedMomentContainmentInputs
    (Measure Observable Configuration Epsilon Witness : Set)
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ)
    (realization :
      Realization.Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData) : Set₁ where
  field
    measureLimit : Limit.SequentialLimit Measure
    momentOrder : Epsilon → Nat

    Admissible : Epsilon → Witness → Set
    Controls : Epsilon → Witness → Measure → Set
    compactWitness : Epsilon → Witness

    renormalized :
      Realization.RenormalizedPath4GaugeEnergyObservable realization

    compactWitnessAdmissible : ∀ epsilon →
      Admissible epsilon (compactWitness epsilon)

    -- This is the exact selected-expectation semantic seam. Once expectation is
    -- known to be the probability integral of `observableValue`, ordinary
    -- Markov/sublevel theory is the intended producer. T5 does not currently
    -- expose that integral semantics, so this theorem remains explicit.
    selectedExpectationMarkovSublevel : ∀ epsilon cutoff →
      Path4PointwiseNonnegative realization
        (Realization.path4GaugeEnergyObservable realization) →
      Path4PointwiseCoercive realization
        (Realization.path4GaugeEnergyObservable realization) →
      Moment.MomentBoundAt (T5.moments expectationData)
        (momentOrder epsilon)
        (Realization.path4GaugeEnergyObservable realization)
        cutoff →
      Controls epsilon (compactWitness epsilon)
        (T5.diagonalMeasure expectationData cutoff)

open Path4SelectedMomentContainmentInputs public

compilePath4MomentCompactContainmentInputs :
  ∀ {Measure Observable Configuration Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ}
    {realization :
      Realization.Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData} →
  Path4SelectedMomentContainmentInputs
    Measure Observable Configuration Epsilon Witness
    expectationData realization →
  Moment.MomentCompactContainmentInputs
    Measure Observable ℚ Epsilon Witness expectationData
compilePath4MomentCompactContainmentInputs
  {realization = realization} inputs = record
  { measureLimit = measureLimit inputs
  ; Admissible = Admissible inputs
  ; Controls = Controls inputs
  ; tightnessObservable = λ epsilon →
      Realization.path4GaugeEnergyObservable realization
  ; momentOrder = momentOrder inputs
  ; compactWitness = compactWitness inputs
  ; tightnessObservableRenormalized = λ epsilon →
      Realization.path4GaugeEnergyRenormalized (renormalized inputs)
  ; compactWitnessAdmissible = compactWitnessAdmissible inputs
  ; momentBoundControlsCompactComplement = λ epsilon cutoff bound →
      selectedExpectationMarkovSublevel inputs epsilon cutoff
        (Realization.path4GaugeEnergyObservablePointwiseNonnegative realization)
        (Realization.path4GaugeEnergyObservablePointwiseCoercive realization)
        bound
  }

path4SelectedMomentContainmentCompilerLevel : ProofLevel
path4SelectedMomentContainmentCompilerLevel = machineChecked

path4FiniteNonnegativityAndCoercivityReuseLevel : ProofLevel
path4FiniteNonnegativityAndCoercivityReuseLevel = machineChecked

physicalSelectedExpectationMarkovSemanticsLevel : ProofLevel
physicalSelectedExpectationMarkovSemanticsLevel = conditional

path4GaugeEnergyCompactSublevelLevel : ProofLevel
path4GaugeEnergyCompactSublevelLevel = conditional
