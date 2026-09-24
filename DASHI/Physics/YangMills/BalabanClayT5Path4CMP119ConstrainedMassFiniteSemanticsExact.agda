module DASHI.Physics.YangMills.BalabanClayT5Path4CMP119ConstrainedMassFiniteSemanticsExact where

------------------------------------------------------------------------
-- CMP119 ASSEMBLED DENSITY = GATE4 CONSTRAINED MASS
--   -> PATH4 FINITE PROBABILITY SEMANTICS
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteSlowDensityExact as Assembled
import DASHI.Physics.YangMills.BalabanCMP119Gate4ConstrainedMassWeldExact as Weld
import DASHI.Physics.YangMills.BalabanCMP119Gate4ConstrainedMassFiniteVolumePresentationExact as Presentation
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Path4
import DASHI.Physics.YangMills.BalabanClayT5Path4FiniteProbabilitySemanticsExact as FinitePath4
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen

record Path4CMP119ConstrainedMassFiniteSemanticsInputs
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
      Weld.CMP119Gate4ConstrainedMassWeld
        source family referenceInputs typed evaluator}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    (finitePresentation :
      Presentation.CMP119ConstrainedMassFiniteVolumeInputs
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

open Path4CMP119ConstrainedMassFiniteSemanticsInputs public

compilePath4CMP119ConstrainedMassFiniteProbabilitySemantics :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed evaluator weld thermodynamic
      finitePresentation diagonal realization} →
  Path4CMP119ConstrainedMassFiniteSemanticsInputs
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
    (Presentation.compileCMP119ConstrainedMassSelectedT5ProbabilityPresentation
      finitePresentation)
    realization
compilePath4CMP119ConstrainedMassFiniteProbabilitySemantics inputs = record
  { observableValueIsApplication =
      observableValueIsApplication inputs
  }

selectedPath4ExpectationIsCMP119ConstrainedMassIntegral :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed evaluator weld thermodynamic
      finitePresentation diagonal realization}
    (inputs :
      Path4CMP119ConstrainedMassFiniteSemanticsInputs
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
    (compilePath4CMP119ConstrainedMassFiniteProbabilitySemantics inputs)
    cutoff
selectedPath4ExpectationIsCMP119ConstrainedMassIntegral inputs cutoff =
  FinitePath4.selectedPath4ExpectationIsFiniteProbabilityIntegral
    (compilePath4CMP119ConstrainedMassFiniteProbabilitySemantics inputs)
    cutoff

path4CMP119ConstrainedMassFiniteSemanticsCompilerLevel : ProofLevel
path4CMP119ConstrainedMassFiniteSemanticsCompilerLevel = machineChecked

path4CMP119ConstrainedMassExpectationIntegralCompilerLevel : ProofLevel
path4CMP119ConstrainedMassExpectationIntegralCompilerLevel = machineChecked

path4CMP119ConstrainedMassObservableEvaluationLevel : ProofLevel
path4CMP119ConstrainedMassObservableEvaluationLevel = conditional
