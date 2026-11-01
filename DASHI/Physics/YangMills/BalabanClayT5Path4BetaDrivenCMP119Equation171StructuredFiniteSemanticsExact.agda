module DASHI.Physics.YangMills.BalabanClayT5Path4BetaDrivenCMP119Equation171StructuredFiniteSemanticsExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FiniteDensityEvaluationExact as SourceEval
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP122Equation171FiniteConstrainedRealizationExact as Finite
import DASHI.Physics.YangMills.BalabanCMP119Equation171FinitePhysicalRealizationExact as Structured
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Equation171StructuredFiniteVolumeExact as Presentation
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Path4
import DASHI.Physics.YangMills.BalabanClayT5Path4FiniteProbabilitySemanticsExact as FinitePath4
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen

record Path4BetaDrivenCMP119Equation171StructuredFiniteSemanticsInputs
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
    {sourceT :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding :
      RingEmbed.RationalRealRingEmbedding}
    {finite :
      Finite.CMP122Equation171FiniteConstrainedRealization
        construction sourceT embedding}
    {realization :
      Structured.CMP119Equation171FinitePhysicalRealization
        source family referenceInputs typed
        (SourceEval.asDownstreamAssemblySemantics sourceSemantics)
        sourceT embedding finite}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    (finitePresentation :
      Presentation.BetaDrivenCMP119Equation171StructuredFiniteVolumeInputs
        source family referenceInputs typed sourceSemantics sourceT
        embedding finite realization thermodynamic)
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

open Path4BetaDrivenCMP119Equation171StructuredFiniteSemanticsInputs public

compilePath4BetaDrivenCMP119StructuredEquation171FiniteProbabilitySemantics :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics sourceT embedding
      finite realization thermodynamic finitePresentation diagonal path4} →
  Path4BetaDrivenCMP119Equation171StructuredFiniteSemanticsInputs
    {trajectory = trajectory} {split = split}
    {source = source} {family = family}
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    {referenceInputs = referenceInputs}
    {typed = typed}
    {sourceSemantics = sourceSemantics}
    {sourceT = sourceT}
    {embedding = embedding}
    {finite = finite}
    {realization = realization}
    {thermodynamic = thermodynamic}
    finitePresentation diagonal path4 →
  FinitePath4.Path4PreferredFiniteProbabilitySemantics
    Measure Fine SlowField
    thermodynamic
    diagonal
    (Presentation.compileBetaDrivenStructuredEquation171SelectedT5ProbabilityPresentation
      finitePresentation)
    path4
compilePath4BetaDrivenCMP119StructuredEquation171FiniteProbabilitySemantics inputs = record
  { observableValueIsApplication =
      observableValueIsApplication inputs
  }

selectedPath4ExpectationIsBetaDrivenCMP119StructuredEquation171Integral :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics sourceT embedding
      finite realization thermodynamic finitePresentation diagonal path4}
    (inputs :
      Path4BetaDrivenCMP119Equation171StructuredFiniteSemanticsInputs
        {trajectory = trajectory} {split = split}
        {source = source} {family = family}
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {Measure = Measure}
        {construction = construction}
        {referenceInputs = referenceInputs}
        {typed = typed}
        {sourceSemantics = sourceSemantics}
        {sourceT = sourceT}
        {embedding = embedding}
        {finite = finite}
        {realization = realization}
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
    (compilePath4BetaDrivenCMP119StructuredEquation171FiniteProbabilitySemantics inputs)
    cutoff
selectedPath4ExpectationIsBetaDrivenCMP119StructuredEquation171Integral inputs cutoff =
  FinitePath4.selectedPath4ExpectationIsFiniteProbabilityIntegral
    (compilePath4BetaDrivenCMP119StructuredEquation171FiniteProbabilitySemantics inputs)
    cutoff

path4BetaDrivenCMP119StructuredEquation171FiniteSemanticsCompilerLevel : ProofLevel
path4BetaDrivenCMP119StructuredEquation171FiniteSemanticsCompilerLevel = machineChecked

path4BetaDrivenCMP119StructuredEquation171ExpectationIntegralCompilerLevel : ProofLevel
path4BetaDrivenCMP119StructuredEquation171ExpectationIntegralCompilerLevel = machineChecked

path4BetaDrivenCMP119StructuredEquation171ObservableEvaluationLevel : ProofLevel
path4BetaDrivenCMP119StructuredEquation171ObservableEvaluationLevel = conditional
