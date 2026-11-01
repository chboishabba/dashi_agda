module DASHI.Physics.YangMills.BalabanClayT5Path4ConditionalGate4FiniteSemanticsExact where

------------------------------------------------------------------------
-- CORRECTED GATE4 CONDITIONAL-MIXTURE ROUTE -> PATH4 FINITE SEMANTICS
--
-- Gate4's normalized reference object is used as a conditional fast-field
-- kernel at fixed slow field.  A normalized slow-field law supplies the coarse
-- marginal.  The fine law is the exact mixture, and the selected T5
-- probability presentation is compiler output.
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
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanFiniteVolumeConditionalGate4PresentationExact as Conditional

record Path4ConditionalGate4FiniteSemanticsInputs
    {Scale Fine SlowField Component Functional Measure : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    (finitePresentation :
      Conditional.ConditionalGate4FiniteVolumePresentationInputs
        referenceInputs typed thermodynamic)
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

open Path4ConditionalGate4FiniteSemanticsInputs public

compilePath4ConditionalFiniteProbabilitySemantics :
  ∀ {Scale Fine SlowField Component Functional Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    {finitePresentation :
      Conditional.ConditionalGate4FiniteVolumePresentationInputs
        referenceInputs typed thermodynamic}
    {diagonal :
      Diagonal.PreferredDiagonalExpectationProducerInputs
        Measure (Reopen.Observable Fine) ℚ thermodynamic}
    {realization :
      Path4.Path4GaugeEnergyObservableRealization
        Measure (Reopen.Observable Fine) Fine
        (Diagonal.compilePreferredDiagonalExpectationProducer diagonal)} →
  Path4ConditionalGate4FiniteSemanticsInputs
    finitePresentation diagonal realization →
  Path4Probability.Path4PreferredFiniteProbabilitySemantics
    Measure Fine SlowField
    thermodynamic
    diagonal
    (Conditional.compileConditionalGate4SelectedT5ProbabilityPresentation
      finitePresentation)
    realization
compilePath4ConditionalFiniteProbabilitySemantics inputs = record
  { observableValueIsApplication =
      observableValueIsApplication inputs
  }

selectedPath4ExpectationIsConditionalGate4FiniteIntegral :
  ∀ {Scale Fine SlowField Component Functional Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    {finitePresentation :
      Conditional.ConditionalGate4FiniteVolumePresentationInputs
        referenceInputs typed thermodynamic}
    {diagonal :
      Diagonal.PreferredDiagonalExpectationProducerInputs
        Measure (Reopen.Observable Fine) ℚ thermodynamic}
    {realization :
      Path4.Path4GaugeEnergyObservableRealization
        Measure (Reopen.Observable Fine) Fine
        (Diagonal.compilePreferredDiagonalExpectationProducer diagonal)}
    (inputs :
      Path4ConditionalGate4FiniteSemanticsInputs
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
    (compilePath4ConditionalFiniteProbabilitySemantics inputs)
    cutoff
selectedPath4ExpectationIsConditionalGate4FiniteIntegral inputs cutoff =
  Path4Probability.selectedPath4ExpectationIsFiniteProbabilityIntegral
    (compilePath4ConditionalFiniteProbabilitySemantics inputs)
    cutoff

path4ConditionalGate4FiniteSemanticsCompilerLevel : ProofLevel
path4ConditionalGate4FiniteSemanticsCompilerLevel = machineChecked

path4ConditionalGate4ExpectationIntegralCompilerLevel : ProofLevel
path4ConditionalGate4ExpectationIntegralCompilerLevel = machineChecked

path4ConditionalObservableEvaluationLevel : ProofLevel
path4ConditionalObservableEvaluationLevel = conditional
