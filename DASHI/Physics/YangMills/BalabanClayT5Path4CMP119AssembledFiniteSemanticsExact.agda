module DASHI.Physics.YangMills.BalabanClayT5Path4CMP119AssembledFiniteSemanticsExact where

------------------------------------------------------------------------
-- ASSEMBLED CMP119 SOURCE DENSITY -> PATH4 FINITE PROBABILITY SEMANTICS
--
-- Preferred source-pinned finite semantic spine:
--
--   Round219 densityAt k = assembleDensity (T_k,A_k)
--     -> finite evaluation of the exact assembled source coordinates
--     -> normalized slow-field law
--     -> corrected Gate4 conditional mixture reopening
--     -> selected T5 finite probability presentation
--     -> Path4 expectation = literal finite probability integral.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteSlowDensityExact as Density
import DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteVolumeGate4PresentationExact as Presentation
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Path4
import DASHI.Physics.YangMills.BalabanClayT5Path4FiniteProbabilitySemanticsExact as FinitePath4
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen

record Path4CMP119AssembledFiniteSemanticsInputs
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
      Density.CMP119AssembledDensityFiniteEvaluator family SlowField}
    {densityRealization :
      Density.CMP119AssembledFiniteSlowDensityRealization
        source family referenceInputs typed evaluator}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    (finitePresentation :
      Presentation.CMP119AssembledGate4FiniteVolumePresentationInputs
        source family referenceInputs typed evaluator
        densityRealization thermodynamic)
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

open Path4CMP119AssembledFiniteSemanticsInputs public

compilePath4CMP119AssembledFiniteProbabilitySemantics :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed evaluator
      densityRealization thermodynamic finitePresentation
      diagonal realization} →
  Path4CMP119AssembledFiniteSemanticsInputs
    {trajectory = trajectory} {split = split}
    {source = source} {family = family}
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    {referenceInputs = referenceInputs}
    {typed = typed}
    {evaluator = evaluator}
    {densityRealization = densityRealization}
    {thermodynamic = thermodynamic}
    finitePresentation diagonal realization →
  FinitePath4.Path4PreferredFiniteProbabilitySemantics
    Measure Fine SlowField
    thermodynamic
    diagonal
    (Presentation.compileCMP119AssembledGate4SelectedT5ProbabilityPresentation
      finitePresentation)
    realization
compilePath4CMP119AssembledFiniteProbabilitySemantics inputs = record
  { observableValueIsApplication =
      observableValueIsApplication inputs
  }

selectedPath4ExpectationIsAssembledCMP119FiniteIntegral :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed evaluator
      densityRealization thermodynamic finitePresentation
      diagonal realization}
    (inputs :
      Path4CMP119AssembledFiniteSemanticsInputs
        {trajectory = trajectory} {split = split}
        {source = source} {family = family}
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {Measure = Measure}
        {construction = construction}
        {referenceInputs = referenceInputs}
        {typed = typed}
        {evaluator = evaluator}
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
    (compilePath4CMP119AssembledFiniteProbabilitySemantics inputs)
    cutoff
selectedPath4ExpectationIsAssembledCMP119FiniteIntegral inputs cutoff =
  FinitePath4.selectedPath4ExpectationIsFiniteProbabilityIntegral
    (compilePath4CMP119AssembledFiniteProbabilitySemantics inputs)
    cutoff

path4CMP119AssembledFiniteSemanticsCompilerLevel : ProofLevel
path4CMP119AssembledFiniteSemanticsCompilerLevel = machineChecked

path4CMP119AssembledExpectationIntegralCompilerLevel : ProofLevel
path4CMP119AssembledExpectationIntegralCompilerLevel = machineChecked

path4CMP119AssembledObservableEvaluationLevel : ProofLevel
path4CMP119AssembledObservableEvaluationLevel = conditional
