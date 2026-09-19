module DASHI.Physics.YangMills.BalabanClayT5Path4CanonicalGate4FiniteSemanticsExact where

------------------------------------------------------------------------
-- CANONICAL GATE4 REOPENING FAMILY -> PATH4 FINITE PROBABILITY SEMANTICS
--
-- This is the shortest preferred finite semantic spine:
--
--   physical coarse/fibre disintegration
--     -> canonical Gate4 reopening step
--     -> canonical Round283 presentation
--     -> canonical selected probability presentation
--     -> Path4 expectation = literal finite probability integral.
--
-- No arbitrary stepAt, probabilityAt or normalized-reference weld remains.
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
import DASHI.Physics.YangMills.BalabanFiniteVolumeCanonicalGate4PresentationExact as Canonical

record Path4CanonicalGate4FiniteSemanticsInputs
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
    (finitePresentation :
      Canonical.CanonicalGate4FiniteVolumePresentationInputs
        referenceInputs thermodynamic)
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

open Path4CanonicalGate4FiniteSemanticsInputs public

compilePath4CanonicalFiniteProbabilitySemantics :
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
    {finitePresentation :
      Canonical.CanonicalGate4FiniteVolumePresentationInputs
        referenceInputs thermodynamic}
    {diagonal :
      Diagonal.PreferredDiagonalExpectationProducerInputs
        Measure (Reopen.Observable Fine) ℚ thermodynamic}
    {realization :
      Path4.Path4GaugeEnergyObservableRealization
        Measure (Reopen.Observable Fine) Fine
        (Diagonal.compilePreferredDiagonalExpectationProducer diagonal)} →
  Path4CanonicalGate4FiniteSemanticsInputs
    finitePresentation diagonal realization →
  Path4Probability.Path4PreferredFiniteProbabilitySemantics
    Measure Fine Coarse
    thermodynamic
    diagonal
    (Canonical.compileCanonicalGate4SelectedT5ProbabilityPresentation
      finitePresentation)
    realization
compilePath4CanonicalFiniteProbabilitySemantics inputs = record
  { observableValueIsApplication =
      observableValueIsApplication inputs
  }

selectedPath4ExpectationIsCanonicalGate4FiniteIntegral :
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
    {finitePresentation :
      Canonical.CanonicalGate4FiniteVolumePresentationInputs
        referenceInputs thermodynamic}
    {diagonal :
      Diagonal.PreferredDiagonalExpectationProducerInputs
        Measure (Reopen.Observable Fine) ℚ thermodynamic}
    {realization :
      Path4.Path4GaugeEnergyObservableRealization
        Measure (Reopen.Observable Fine) Fine
        (Diagonal.compilePreferredDiagonalExpectationProducer diagonal)}
    (inputs :
      Path4CanonicalGate4FiniteSemanticsInputs
        finitePresentation diagonal realization)
    cutoff →
  Gram.expectation
    (T5.operations thermodynamic)
    (T5.diagonalMeasure
      (Diagonal.compilePreferredDiagonalExpectationProducer diagonal)
      cutoff)
    (Path4.path4GaugeEnergyObservable realization)
  ≡
  Path4Probability.path4FiniteProbabilityIntegral
    (compilePath4CanonicalFiniteProbabilitySemantics inputs)
    cutoff
selectedPath4ExpectationIsCanonicalGate4FiniteIntegral inputs cutoff =
  Path4Probability.selectedPath4ExpectationIsFiniteProbabilityIntegral
    (compilePath4CanonicalFiniteProbabilitySemantics inputs)
    cutoff

path4CanonicalGate4FiniteSemanticsCompilerLevel : ProofLevel
path4CanonicalGate4FiniteSemanticsCompilerLevel = machineChecked

path4CanonicalGate4ExpectationIntegralCompilerLevel : ProofLevel
path4CanonicalGate4ExpectationIntegralCompilerLevel = machineChecked

path4CanonicalObservableEvaluationLevel : ProofLevel
path4CanonicalObservableEvaluationLevel = conditional
