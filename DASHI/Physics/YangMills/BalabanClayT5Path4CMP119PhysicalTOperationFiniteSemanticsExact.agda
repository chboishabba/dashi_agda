module DASHI.Physics.YangMills.BalabanClayT5Path4CMP119PhysicalTOperationFiniteSemanticsExact where

------------------------------------------------------------------------
-- CMP119 ASSEMBLED DENSITY = PHYSICAL T-OPERATION AT 1
--   -> PATH4 FINITE PROBABILITY SEMANTICS
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteSlowDensityExact as Assembled
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationWeldExact as Weld
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationFiniteVolumePresentationExact as Presentation
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Path4
import DASHI.Physics.YangMills.BalabanClayT5Path4FiniteProbabilitySemanticsExact as FinitePath4
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen

record Path4CMP119PhysicalTOperationFiniteSemanticsInputs
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
    {evaluator :
      Assembled.CMP119AssembledDensityFiniteEvaluator family SlowField}
    {weld :
      Weld.CMP119PhysicalTOperationWeld
        source family referenceInputs typed evaluator}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    (finitePresentation :
      Presentation.CMP119PhysicalTOperationFiniteVolumeInputs
        source family referenceInputs typed evaluator weld thermodynamic)
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

open Path4CMP119PhysicalTOperationFiniteSemanticsInputs public

compilePath4CMP119PhysicalTOperationFiniteProbabilitySemantics :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed evaluator weld thermodynamic
      finitePresentation diagonal realization} →
  Path4CMP119PhysicalTOperationFiniteSemanticsInputs
    {trajectory = trajectory} {split = split}
    {source = source} {family = family}
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    {referenceInputs = referenceInputs}
    {typed = typed}
    {evaluator = evaluator} {weld = weld}
    {thermodynamic = thermodynamic}
    finitePresentation diagonal realization →
  FinitePath4.Path4PreferredFiniteProbabilitySemantics
    Measure Fine SlowField
    thermodynamic
    diagonal
    (Presentation.compileCMP119PhysicalTOperationSelectedT5ProbabilityPresentation
      finitePresentation)
    realization
compilePath4CMP119PhysicalTOperationFiniteProbabilitySemantics inputs = record
  { observableValueIsApplication =
      observableValueIsApplication inputs
  }

selectedPath4ExpectationIsCMP119PhysicalTOperationIntegral :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed evaluator weld thermodynamic
      finitePresentation diagonal realization}
    (inputs :
      Path4CMP119PhysicalTOperationFiniteSemanticsInputs
        {trajectory = trajectory} {split = split}
        {source = source} {family = family}
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {Measure = Measure}
        {construction = construction}
        {referenceInputs = referenceInputs}
        {typed = typed}
        {evaluator = evaluator} {weld = weld}
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
    (compilePath4CMP119PhysicalTOperationFiniteProbabilitySemantics inputs)
    cutoff
selectedPath4ExpectationIsCMP119PhysicalTOperationIntegral inputs cutoff =
  FinitePath4.selectedPath4ExpectationIsFiniteProbabilityIntegral
    (compilePath4CMP119PhysicalTOperationFiniteProbabilitySemantics inputs)
    cutoff

path4CMP119PhysicalTOperationFiniteSemanticsCompilerLevel : ProofLevel
path4CMP119PhysicalTOperationFiniteSemanticsCompilerLevel = machineChecked

path4CMP119PhysicalTOperationExpectationIntegralCompilerLevel : ProofLevel
path4CMP119PhysicalTOperationExpectationIntegralCompilerLevel = machineChecked

path4CMP119PhysicalTOperationObservableEvaluationLevel : ProofLevel
path4CMP119PhysicalTOperationObservableEvaluationLevel = conditional
