module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119PhysicalTOperationFiniteVolumeExact where

------------------------------------------------------------------------
-- SOURCE-FIXED BETA-DRIVEN CMP119 EVALUATION + PHYSICAL T REALIZATION
--   -> FINITE T5 PRESENTATION
--
-- The finite density assembly semantics are now owned at the source-family
-- boundary.  Downstream users cannot choose another assembleDensity meaning.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FiniteDensityEvaluationExact as SourceEval
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationAssemblyRealizationExact as Realization
import DASHI.Physics.YangMills.BalabanCMP119SplitPhysicalTOperationFiniteVolumePresentationExact as Split
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact as R283
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Probability
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayGate4RawSlowDensityToProbabilityExact as Raw
import DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteSlowDensityExact as Assembled
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationWeldExact as Weld

record BetaDrivenCMP119PhysicalTOperationFiniteVolumeInputs
    {trajectory split}
    (source :
      Beta.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split})
    (family : R219.BetaDrivenCMP119ResidualFamily source)
    {Scale Fine SlowField Component Functional Measure : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    (typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs)
    (sourceSemantics :
      SourceEval.BetaDrivenCMP119FiniteDensityEvaluation
        source family SlowField)
    (realization :
      Realization.CMP119PhysicalTOperationAssemblyRealization
        source family referenceInputs typed
        (SourceEval.asDownstreamAssemblySemantics sourceSemantics))
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    finiteVolumeExpectationIsSourceFixedPhysicalTOperationExpectation :
      ∀ cutoff observable →
      Gram.expectation (T5.operations thermodynamic)
        (Diagonal.selectedFiniteVolumeSequence thermodynamic cutoff)
        observable
      ≡
      Reopen.fineExpectation
        (Raw.compileRawSlowDensityReopeningStep
          (Assembled.compileAssembledSelectedDensityRawSlowLaw
            (Weld.compileCMP119PhysicalTOperationFiniteSlowDensityRealization
              (Realization.compileEndToEndPhysicalTOperationWeld realization))
            cutoff))
        observable

open BetaDrivenCMP119PhysicalTOperationFiniteVolumeInputs public

asSplitFiniteVolumeInputs :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics realization thermodynamic} →
  BetaDrivenCMP119PhysicalTOperationFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics realization thermodynamic →
  Split.CMP119SplitPhysicalTOperationFiniteVolumeInputs
    source family referenceInputs typed
    (SourceEval.asDownstreamAssemblySemantics sourceSemantics)
    realization thermodynamic
asSplitFiniteVolumeInputs inputs = record
  { finiteVolumeExpectationIsSplitPhysicalTOperationMixtureExpectation =
      finiteVolumeExpectationIsSourceFixedPhysicalTOperationExpectation inputs
  }

compileBetaDrivenCMP119Round283Presentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics realization thermodynamic} →
  BetaDrivenCMP119PhysicalTOperationFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics realization thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine SlowField thermodynamic
compileBetaDrivenCMP119Round283Presentation inputs =
  Split.compileCMP119SplitPhysicalTOperationRound283Presentation
    (asSplitFiniteVolumeInputs inputs)

compileBetaDrivenCMP119SelectedT5ProbabilityPresentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics realization thermodynamic} →
  BetaDrivenCMP119PhysicalTOperationFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics realization thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine SlowField thermodynamic
compileBetaDrivenCMP119SelectedT5ProbabilityPresentation inputs =
  Split.compileCMP119SplitPhysicalTOperationSelectedT5ProbabilityPresentation
    (asSplitFiniteVolumeInputs inputs)

betaDrivenCMP119Round283CompilerLevel : ProofLevel
betaDrivenCMP119Round283CompilerLevel = machineChecked

betaDrivenCMP119SelectedProbabilityCompilerLevel : ProofLevel
betaDrivenCMP119SelectedProbabilityCompilerLevel = machineChecked

-- Surviving finite same-object payment after source semantics are fixed.
betaDrivenCMP119ToT5ExpectationSameObjectLevel : ProofLevel
betaDrivenCMP119ToT5ExpectationSameObjectLevel = conditional
