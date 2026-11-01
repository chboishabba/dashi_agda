module DASHI.Physics.YangMills.BalabanClayT5Path4PreferredGate4ProbabilitySemanticsExact where

------------------------------------------------------------------------
-- PREFERRED GATE4 PROBABILITY LAW -> PATH4 T5 EXPECTATION SEMANTICS
--
-- The earlier Path4 finite-probability weld accepted an arbitrary selected T5
-- probability presentation.  The preferred Gate4 route now constructs that
-- presentation from the normalized reference/reopening same-object data.
--
-- This module composes the two layers.  On this route, the Path4 expectation
-- integral theorem depends only on:
--
--   * the preferred Gate4 reference/reopening same-object inputs;
--   * the preferred T5 finite-volume expectation producer;
--   * the literal Path4 observable realization on the same Fine carrier;
--   * observableValue O x = O x.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Path4
import DASHI.Physics.YangMills.BalabanClayT5Path4FiniteProbabilitySemanticsExact as Path4Probability
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4PreferredSelectedProbabilityExact as Gate4Probability
import DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact as R283

record Path4PreferredGate4ProbabilityInputs
    {Scale Fine SlowField Component Functional Coarse Measure : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    {presentation :
      R283.FiniteVolumeReopeningPresentation
        Measure Fine Coarse thermodynamic}
    (gate4Probability :
      Gate4Probability.PreferredSelectedProbabilityInputs
        referenceInputs thermodynamic presentation)
    (diagonal :
      Diagonal.PreferredDiagonalExpectationProducerInputs
        Measure (Reopen.Observable Fine) ℚ thermodynamic)
    (realization :
      Path4.Path4GaugeEnergyObservableRealization
        Measure (Reopen.Observable Fine) Fine
        (Diagonal.compilePreferredDiagonalExpectationProducer diagonal)) : Set₁ where
  field
    observableValueIsApplication :
      ∀ observable fine →
      Path4.observableValue realization observable fine
      ≡ observable fine

open Path4PreferredGate4ProbabilityInputs public

compilePath4PreferredFiniteProbabilitySemantics :
  ∀ {Scale Fine SlowField Component Functional Coarse Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    {presentation :
      R283.FiniteVolumeReopeningPresentation
        Measure Fine Coarse thermodynamic}
    {gate4Probability :
      Gate4Probability.PreferredSelectedProbabilityInputs
        referenceInputs thermodynamic presentation}
    {diagonal :
      Diagonal.PreferredDiagonalExpectationProducerInputs
        Measure (Reopen.Observable Fine) ℚ thermodynamic}
    {realization :
      Path4.Path4GaugeEnergyObservableRealization
        Measure (Reopen.Observable Fine) Fine
        (Diagonal.compilePreferredDiagonalExpectationProducer diagonal)} →
  Path4PreferredGate4ProbabilityInputs
    gate4Probability diagonal realization →
  Path4Probability.Path4PreferredFiniteProbabilitySemantics
    Measure Fine Coarse
    thermodynamic
    diagonal
    (Gate4Probability.compilePreferredSelectedT5ProbabilityPresentation
      gate4Probability)
    realization
compilePath4PreferredFiniteProbabilitySemantics
  inputs = record
  { observableValueIsApplication =
      observableValueIsApplication inputs
  }

selectedPath4ExpectationIsGate4FiniteProbabilityIntegral :
  ∀ {Scale Fine SlowField Component Functional Coarse Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    {presentation :
      R283.FiniteVolumeReopeningPresentation
        Measure Fine Coarse thermodynamic}
    {gate4Probability :
      Gate4Probability.PreferredSelectedProbabilityInputs
        referenceInputs thermodynamic presentation}
    {diagonal :
      Diagonal.PreferredDiagonalExpectationProducerInputs
        Measure (Reopen.Observable Fine) ℚ thermodynamic}
    {realization :
      Path4.Path4GaugeEnergyObservableRealization
        Measure (Reopen.Observable Fine) Fine
        (Diagonal.compilePreferredDiagonalExpectationProducer diagonal)}
    (inputs :
      Path4PreferredGate4ProbabilityInputs
        gate4Probability diagonal realization)
    cutoff →
  Gram.expectation
    (T5.operations thermodynamic)
    (T5.diagonalMeasure
      (Diagonal.compilePreferredDiagonalExpectationProducer diagonal)
      cutoff)
    (Path4.path4GaugeEnergyObservable realization)
  ≡
  Path4Probability.path4FiniteProbabilityIntegral
    (compilePath4PreferredFiniteProbabilitySemantics inputs)
    cutoff
selectedPath4ExpectationIsGate4FiniteProbabilityIntegral inputs cutoff =
  Path4Probability.selectedPath4ExpectationIsFiniteProbabilityIntegral
    (compilePath4PreferredFiniteProbabilitySemantics inputs)
    cutoff

path4PreferredGate4ProbabilityCompilerLevel : ProofLevel
path4PreferredGate4ProbabilityCompilerLevel = machineChecked

path4Gate4ExpectationIntegralWeldLevel : ProofLevel
path4Gate4ExpectationIntegralWeldLevel = machineChecked

-- The remaining same-object semantic input on this layer is evaluation.
path4ObservableApplicationMeaningLevel : ProofLevel
path4ObservableApplicationMeaningLevel = conditional
