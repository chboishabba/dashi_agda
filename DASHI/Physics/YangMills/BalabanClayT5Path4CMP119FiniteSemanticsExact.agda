module DASHI.Physics.YangMills.BalabanClayT5Path4CMP119FiniteSemanticsExact where

------------------------------------------------------------------------
-- CMP119 SELECTED DENSITY -> PATH4 FINITE PROBABILITY SEMANTICS
--
-- This is the preferred finite semantic source spine after the Gate4
-- conditional-kernel correction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as CMP119
import DASHI.Physics.YangMills.BalabanCMP119FiniteSlowDensityRealizationExact as Density
import DASHI.Physics.YangMills.BalabanCMP119FiniteVolumeGate4PresentationExact as Presentation
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Path4
import DASHI.Physics.YangMills.BalabanClayT5Path4FiniteProbabilitySemanticsExact as FinitePath4
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen

record Path4CMP119FiniteSemanticsInputs
    {trajectory split}
    {source :
      CMP119.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split}}
    {Scale Fine SlowField Component Functional Measure : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs}
    {densityRealization :
      Density.CMP119FiniteSlowDensityRealization
        source referenceInputs typed}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    (finitePresentation :
      Presentation.CMP119Gate4FiniteVolumePresentationInputs
        source referenceInputs typed densityRealization thermodynamic)
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

open Path4CMP119FiniteSemanticsInputs public

compilePath4CMP119FiniteProbabilitySemantics :
  ∀ {trajectory split source
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed densityRealization thermodynamic
      finitePresentation diagonal realization} →
  Path4CMP119FiniteSemanticsInputs
    {trajectory = trajectory} {split = split}
    {source = source}
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    {referenceInputs = referenceInputs}
    {typed = typed}
    {densityRealization = densityRealization}
    {thermodynamic = thermodynamic}
    finitePresentation diagonal realization →
  FinitePath4.Path4PreferredFiniteProbabilitySemantics
    Measure Fine SlowField
    thermodynamic
    diagonal
    (Presentation.compileCMP119Gate4SelectedT5ProbabilityPresentation
      finitePresentation)
    realization
compilePath4CMP119FiniteProbabilitySemantics inputs = record
  { observableValueIsApplication =
      observableValueIsApplication inputs
  }

selectedPath4ExpectationIsCMP119FiniteIntegral :
  ∀ {trajectory split source
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed densityRealization thermodynamic
      finitePresentation diagonal realization}
    (inputs :
      Path4CMP119FiniteSemanticsInputs
        {trajectory = trajectory} {split = split}
        {source = source}
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {Measure = Measure}
        {construction = construction}
        {referenceInputs = referenceInputs}
        {typed = typed}
        {densityRealization = densityRealization}
        {thermodynamic = thermodynamic}
        finitePresentation diagonal realization)
    cutoff →
  Gram.expectation
    (T5.operations thermodynamic)
    (T5.diagonalMeasure
      (Diagonal.compilePreferredDiagonalExpectationProducer diagonal)
      cutoff)
    (Path4.path4GaugeEnergyObservable realization)
  ≡
  FinitePath4.path4FiniteProbabilityIntegral
    (compilePath4CMP119FiniteProbabilitySemantics inputs)
    cutoff
selectedPath4ExpectationIsCMP119FiniteIntegral inputs cutoff =
  FinitePath4.selectedPath4ExpectationIsFiniteProbabilityIntegral
    (compilePath4CMP119FiniteProbabilitySemantics inputs)
    cutoff

path4CMP119FiniteSemanticsCompilerLevel : ProofLevel
path4CMP119FiniteSemanticsCompilerLevel = machineChecked

path4CMP119ExpectationIntegralCompilerLevel : ProofLevel
path4CMP119ExpectationIntegralCompilerLevel = machineChecked

path4CMP119ObservableEvaluationLevel : ProofLevel
path4CMP119ObservableEvaluationLevel = conditional
