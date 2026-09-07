{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyMarkovBridgeExact where

------------------------------------------------------------------------
-- LITERAL PATH4 ENERGY SEMANTICS -> PREFERRED MARKOV/TIGHTNESS BRIDGE
--
-- The generic Markov interface carries predicates named NonnegativeObservable
-- and CoerciveForSelectedTopology.  On the preferred physical route we make
-- those predicates literal pointwise statements about the already-realized
-- Path4 gauge energy, rather than leaving them as opaque physical leaves.
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
import DASHI.Physics.YangMills.BalabanClayT5CoerciveMomentMarkovContainmentExact as Coercive
import DASHI.Physics.YangMills.BalabanClayT5PreferredPhysicalCoerciveMomentBridgeExact as Preferred
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

record Path4MarkovAuthorityInputs
    (Measure Observable Configuration Epsilon Witness : Set)
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ)
    (realization :
      Realization.Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData) : Set₁ where
  field
    Admissible : Epsilon → Witness → Set
    Controls : Epsilon → Witness → Measure → Set
    sublevelWitness : Observable → Nat → Epsilon → Witness

    -- Standard probability/topology authority after the pointwise semantics
    -- have been fixed.  No Yang--Mills coercivity estimate is hidden here.
    markovMomentBoundControlsSublevelComplement :
      (producer :
        T5.ExponentialMomentProducer
          (T5.operations (T5.thermodynamic expectationData))
          (T5.diagonalMeasure expectationData)
          (T5.RenormalizedObservable (T5.thermodynamic expectationData))) →
      (observable : Observable) →
      (degree : Nat) →
      (epsilon : Epsilon) →
      (cutoff : Nat) →
      Path4PointwiseNonnegative realization observable →
      Path4PointwiseCoercive realization observable →
      Admissible epsilon (sublevelWitness observable degree epsilon) →
      Moment.MomentBoundAt producer degree observable cutoff →
      Controls epsilon
        (sublevelWitness observable degree epsilon)
        (T5.diagonalMeasure expectationData cutoff)

open Path4MarkovAuthorityInputs public

compilePath4MarkovAuthority :
  ∀ {Measure Observable Configuration Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ}
    {realization :
      Realization.Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData} →
  Path4MarkovAuthorityInputs
    Measure Observable Configuration Epsilon Witness expectationData realization →
  Coercive.MarkovCompactContainmentAuthority
    Measure Observable ℚ Epsilon Witness
compilePath4MarkovAuthority {expectationData = expectationData} inputs = record
  { Admissible = Admissible inputs
  ; Controls = Controls inputs
  ; NonnegativeObservable = Path4PointwiseNonnegative _
  ; CoerciveForSelectedTopology = Path4PointwiseCoercive _
  ; sublevelWitness = sublevelWitness inputs
  ; markovMomentBoundControlsSublevelComplement =
      λ producer observable degree epsilon cutoff nonnegative coercive compact bound →
        markovMomentBoundControlsSublevelComplement inputs
          producer observable degree epsilon cutoff
          nonnegative coercive compact bound
  }

record Path4PreferredCoerciveMomentInputs
    (Measure Observable Configuration Epsilon Witness : Set)
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ)
    (realization :
      Realization.Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData)
    (markovInputs :
      Path4MarkovAuthorityInputs
        Measure Observable Configuration Epsilon Witness
        expectationData realization) : Set₁ where
  field
    measureLimit : Limit.SequentialLimit Measure
    momentOrder : Epsilon → Nat

    renormalized :
      Realization.RenormalizedPath4GaugeEnergyObservable realization

    compactSublevel : ∀ epsilon →
      Admissible markovInputs epsilon
        (sublevelWitness markovInputs
          (Realization.path4GaugeEnergyObservable realization)
          (momentOrder epsilon)
          epsilon)

open Path4PreferredCoerciveMomentInputs public

compilePath4PreferredCoerciveMomentInputs :
  ∀ {Measure Observable Configuration Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable ℚ}
    {realization :
      Realization.Path4GaugeEnergyObservableRealization
        Measure Observable Configuration expectationData}
    {markovInputs :
      Path4MarkovAuthorityInputs
        Measure Observable Configuration Epsilon Witness
        expectationData realization} →
  Path4PreferredCoerciveMomentInputs
    Measure Observable Configuration Epsilon Witness
    expectationData realization markovInputs →
  Preferred.PreferredPhysicalCoerciveMomentInputs
    Measure Observable ℚ Epsilon Witness expectationData
    (compilePath4MarkovAuthority markovInputs)
compilePath4PreferredCoerciveMomentInputs {realization = realization} inputs = record
  { measureLimit = measureLimit inputs
  ; physicalCoerciveObservable = λ epsilon →
      Realization.path4GaugeEnergyObservable realization
  ; coerciveMomentOrder = momentOrder inputs
  ; physicalCoerciveObservableRenormalized = λ epsilon →
      Realization.path4GaugeEnergyRenormalized (renormalized inputs)
  ; physicalCoerciveObservableNonnegative = λ epsilon →
      Realization.path4GaugeEnergyObservablePointwiseNonnegative realization
  ; physicalCoerciveObservableCoercive = λ epsilon →
      Realization.path4GaugeEnergyObservablePointwiseCoercive realization
  ; physicalCoerciveSublevelCompactInSelectedTopology = compactSublevel inputs
  }

path4PointwiseMarkovAuthorityCompilerLevel : ProofLevel
path4PointwiseMarkovAuthorityCompilerLevel = machineChecked

path4FiniteNonnegativityAndCoercivityReuseLevel : ProofLevel
path4FiniteNonnegativityAndCoercivityReuseLevel = machineChecked

path4MarkovProbabilityAuthorityLevel : ProofLevel
path4MarkovProbabilityAuthorityLevel = standardImported

path4GaugeEnergyCompactSublevelLevel : ProofLevel
path4GaugeEnergyCompactSublevelLevel = conditional
