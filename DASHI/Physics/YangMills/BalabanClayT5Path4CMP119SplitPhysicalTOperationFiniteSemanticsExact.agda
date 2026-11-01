module DASHI.Physics.YangMills.BalabanClayT5Path4CMP119SplitPhysicalTOperationFiniteSemanticsExact where

------------------------------------------------------------------------
-- SPLIT CMP119 ASSEMBLY SEMANTICS -> PHYSICAL T -> PATH4
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact as Assembly
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationAssemblyRealizationExact as Realization
import DASHI.Physics.YangMills.BalabanCMP119SplitPhysicalTOperationFiniteVolumePresentationExact as Presentation
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Path4
import DASHI.Physics.YangMills.BalabanClayT5Path4FiniteProbabilitySemanticsExact as FinitePath4
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen

record Path4CMP119SplitPhysicalTOperationFiniteSemanticsInputs
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
    {semantics :
      Assembly.CMP119FiniteDensityAssemblySemantics
        source family SlowField}
    {realization :
      Realization.CMP119PhysicalTOperationAssemblyRealization
        source family referenceInputs typed semantics}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    (finitePresentation :
      Presentation.CMP119SplitPhysicalTOperationFiniteVolumeInputs
        source family referenceInputs typed semantics
        realization thermodynamic)
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

open Path4CMP119SplitPhysicalTOperationFiniteSemanticsInputs public

compilePath4CMP119SplitPhysicalTOperationFiniteProbabilitySemantics :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed semantics realization thermodynamic
      finitePresentation diagonal path4} →
  Path4CMP119SplitPhysicalTOperationFiniteSemanticsInputs
    {trajectory = trajectory} {split = split}
    {source = source} {family = family}
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    {referenceInputs = referenceInputs}
    {typed = typed}
    {semantics = semantics}
    {realization = realization}
    {thermodynamic = thermodynamic}
    finitePresentation diagonal path4 →
  FinitePath4.Path4PreferredFiniteProbabilitySemantics
    Measure Fine SlowField
    thermodynamic
    diagonal
    (Presentation.compileCMP119SplitPhysicalTOperationSelectedT5ProbabilityPresentation
      finitePresentation)
    path4
compilePath4CMP119SplitPhysicalTOperationFiniteProbabilitySemantics inputs = record
  { observableValueIsApplication =
      observableValueIsApplication inputs
  }

selectedPath4ExpectationIsCMP119SplitPhysicalTOperationIntegral :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed semantics realization thermodynamic
      finitePresentation diagonal path4}
    (inputs :
      Path4CMP119SplitPhysicalTOperationFiniteSemanticsInputs
        {trajectory = trajectory} {split = split}
        {source = source} {family = family}
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {Measure = Measure}
        {construction = construction}
        {referenceInputs = referenceInputs}
        {typed = typed}
        {semantics = semantics}
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
    (compilePath4CMP119SplitPhysicalTOperationFiniteProbabilitySemantics inputs)
    cutoff
selectedPath4ExpectationIsCMP119SplitPhysicalTOperationIntegral inputs cutoff =
  FinitePath4.selectedPath4ExpectationIsFiniteProbabilityIntegral
    (compilePath4CMP119SplitPhysicalTOperationFiniteProbabilitySemantics inputs)
    cutoff

path4CMP119SplitPhysicalTOperationFiniteSemanticsCompilerLevel : ProofLevel
path4CMP119SplitPhysicalTOperationFiniteSemanticsCompilerLevel = machineChecked

path4CMP119SplitPhysicalTOperationExpectationIntegralCompilerLevel : ProofLevel
path4CMP119SplitPhysicalTOperationExpectationIntegralCompilerLevel = machineChecked

path4CMP119SplitPhysicalTOperationObservableEvaluationLevel : ProofLevel
path4CMP119SplitPhysicalTOperationObservableEvaluationLevel = conditional
