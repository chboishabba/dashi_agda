module DASHI.Physics.YangMills.BalabanClayT5Path4BetaDrivenCMP119GeneratedActionFiniteSemanticsExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FiniteDensityEvaluationExact as SourceEval
import DASHI.Physics.YangMills.BalabanCMP119PhysicalEffectiveActionRealizationExact as Generated
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119GeneratedActionFiniteVolumeExact as Presentation
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Path4
import DASHI.Physics.YangMills.BalabanClayT5Path4FiniteProbabilitySemanticsExact as FinitePath4
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen

record Path4BetaDrivenCMP119GeneratedActionFiniteSemanticsInputs
    {trajectory split}
    {source :
      Beta.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split}}
    {family : R219.BetaDrivenCMP119ResidualFamily source}
    {Scale Fine SlowField Component Functional Measure : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs}
    {sourceSemantics :
      SourceEval.BetaDrivenCMP119FiniteDensityEvaluation
        source family SlowField}
    {generatedAction :
      Generated.CMP119PhysicalEffectiveActionRealization
        source family referenceInputs typed
        (SourceEval.asDownstreamAssemblySemantics sourceSemantics)}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    (finitePresentation :
      Presentation.BetaDrivenCMP119GeneratedActionFiniteVolumeInputs
        source family referenceInputs typed sourceSemantics
        generatedAction thermodynamic)
    (diagonal :
      Diagonal.PreferredDiagonalExpectationProducerInputs
        Measure (Reopen.Observable Fine) ℚ thermodynamic)
    (path4 :
      Path4.Path4GaugeEnergyObservableRealization
        Measure (Reopen.Observable Fine) Fine
        (Diagonal.compilePreferredDiagonalExpectationProducer diagonal)) : Set₁ where
  field
    observableValueIsApplication :
      ∀ observable fine →
      Path4.observableValue path4 observable fine
      ≡ observable fine

open Path4BetaDrivenCMP119GeneratedActionFiniteSemanticsInputs public

compilePath4BetaDrivenCMP119GeneratedActionFiniteProbabilitySemantics :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics generatedAction thermodynamic
      finitePresentation diagonal path4} →
  Path4BetaDrivenCMP119GeneratedActionFiniteSemanticsInputs
    {trajectory = trajectory} {split = split}
    {source = source} {family = family}
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    {referenceInputs = referenceInputs}
    {typed = typed}
    {sourceSemantics = sourceSemantics}
    {generatedAction = generatedAction}
    {thermodynamic = thermodynamic}
    finitePresentation diagonal path4 →
  FinitePath4.Path4PreferredFiniteProbabilitySemantics
    Measure Fine SlowField
    thermodynamic
    diagonal
    (Presentation.compileBetaDrivenGeneratedActionSelectedT5ProbabilityPresentation
      finitePresentation)
    path4
compilePath4BetaDrivenCMP119GeneratedActionFiniteProbabilitySemantics inputs = record
  { observableValueIsApplication =
      observableValueIsApplication inputs
  }

selectedPath4ExpectationIsBetaDrivenCMP119GeneratedActionIntegral :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics generatedAction thermodynamic
      finitePresentation diagonal path4}
    (inputs :
      Path4BetaDrivenCMP119GeneratedActionFiniteSemanticsInputs
        {trajectory = trajectory} {split = split}
        {source = source} {family = family}
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {Measure = Measure}
        {construction = construction}
        {referenceInputs = referenceInputs}
        {typed = typed}
        {sourceSemantics = sourceSemantics}
        {generatedAction = generatedAction}
        {thermodynamic = thermodynamic}
        finitePresentation diagonal path4)
    cutoff →
  Gram.expectation
    (T5.operations thermodynamic)
    (T5.diagonalMeasure
      (Diagonal.compilePreferredDiagonalExpectationProducer diagonal)
      cutoff)
    (Path4.path4GaugeEnergyObservable path4)
  ≡
  FinitePath4.path4FiniteProbabilityIntegral
    (compilePath4BetaDrivenCMP119GeneratedActionFiniteProbabilitySemantics inputs)
    cutoff
selectedPath4ExpectationIsBetaDrivenCMP119GeneratedActionIntegral inputs cutoff =
  FinitePath4.selectedPath4ExpectationIsFiniteProbabilityIntegral
    (compilePath4BetaDrivenCMP119GeneratedActionFiniteProbabilitySemantics inputs)
    cutoff

path4BetaDrivenCMP119GeneratedActionFiniteSemanticsCompilerLevel : ProofLevel
path4BetaDrivenCMP119GeneratedActionFiniteSemanticsCompilerLevel = machineChecked

path4BetaDrivenCMP119GeneratedActionExpectationIntegralCompilerLevel : ProofLevel
path4BetaDrivenCMP119GeneratedActionExpectationIntegralCompilerLevel = machineChecked

path4BetaDrivenCMP119GeneratedActionObservableEvaluationLevel : ProofLevel
path4BetaDrivenCMP119GeneratedActionObservableEvaluationLevel = conditional
