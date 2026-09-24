module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Equation171StructuredFiniteVolumeExact where

------------------------------------------------------------------------
-- SOURCE-FIXED CMP119 + STRUCTURED EQ.(1.71) FINITE REALIZATION
--   -> FINITE T5 PRESENTATION
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FiniteDensityEvaluationExact as SourceEval
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP122Equation171FiniteConstrainedRealizationExact as Finite
import DASHI.Physics.YangMills.BalabanCMP119Equation171FinitePhysicalRealizationExact as Structured
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119PhysicalTOperationFiniteVolumeExact as Previous
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
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationAssemblyRealizationExact as PhysicalRealization

record BetaDrivenCMP119Equation171StructuredFiniteVolumeInputs
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
    (sourceT :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField)
    (embedding :
      RingEmbed.RationalRealRingEmbedding)
    (finite :
      Finite.CMP122Equation171FiniteConstrainedRealization
        construction sourceT embedding)
    (realization :
      Structured.CMP119Equation171FinitePhysicalRealization
        source family referenceInputs typed
        (SourceEval.asDownstreamAssemblySemantics sourceSemantics)
        sourceT embedding finite)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    finiteVolumeExpectationIsStructuredEquation171MixtureExpectation :
      ∀ cutoff observable →
      Gram.expectation (T5.operations thermodynamic)
        (Diagonal.selectedFiniteVolumeSequence thermodynamic cutoff)
        observable
      ≡
      Reopen.fineExpectation
        (Raw.compileRawSlowDensityReopeningStep
          (Assembled.compileAssembledSelectedDensityRawSlowLaw
            (Weld.compileCMP119PhysicalTOperationFiniteSlowDensityRealization
              (PhysicalRealization.compileEndToEndPhysicalTOperationWeld
                (Structured.compilePhysicalTOperationAssemblyRealization
                  realization)))
            cutoff))
        observable

open BetaDrivenCMP119Equation171StructuredFiniteVolumeInputs public

asPreviousFiniteVolumeInputs :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics sourceT embedding
      finite realization thermodynamic} →
  BetaDrivenCMP119Equation171StructuredFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics sourceT embedding finite
    realization thermodynamic →
  Previous.BetaDrivenCMP119PhysicalTOperationFiniteVolumeInputs
    source family referenceInputs typed sourceSemantics
    (Structured.compilePhysicalTOperationAssemblyRealization realization)
    thermodynamic
asPreviousFiniteVolumeInputs inputs = record
  { finiteVolumeExpectationIsSourceFixedPhysicalTOperationExpectation =
      finiteVolumeExpectationIsStructuredEquation171MixtureExpectation inputs
  }

compileBetaDrivenStructuredEquation171Round283Presentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics sourceT embedding
      finite realization thermodynamic} →
  BetaDrivenCMP119Equation171StructuredFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics sourceT embedding finite
    realization thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine SlowField thermodynamic
compileBetaDrivenStructuredEquation171Round283Presentation inputs =
  Previous.compileBetaDrivenCMP119Round283Presentation
    (asPreviousFiniteVolumeInputs inputs)

compileBetaDrivenStructuredEquation171SelectedT5ProbabilityPresentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics sourceT embedding
      finite realization thermodynamic} →
  BetaDrivenCMP119Equation171StructuredFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics sourceT embedding finite
    realization thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine SlowField thermodynamic
compileBetaDrivenStructuredEquation171SelectedT5ProbabilityPresentation inputs =
  Previous.compileBetaDrivenCMP119SelectedT5ProbabilityPresentation
    (asPreviousFiniteVolumeInputs inputs)

betaDrivenStructuredEquation171Round283CompilerLevel : ProofLevel
betaDrivenStructuredEquation171Round283CompilerLevel = machineChecked

betaDrivenStructuredEquation171SelectedProbabilityCompilerLevel : ProofLevel
betaDrivenStructuredEquation171SelectedProbabilityCompilerLevel = machineChecked

betaDrivenStructuredEquation171ToT5ExpectationSameObjectLevel : ProofLevel
betaDrivenStructuredEquation171ToT5ExpectationSameObjectLevel = conditional
