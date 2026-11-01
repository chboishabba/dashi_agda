module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119GeneratedActionFiniteVolumeExact where

------------------------------------------------------------------------
-- SOURCE-FIXED CMP119 + GENERATED PHYSICAL EFFECTIVE ACTION
--   -> FINITE T5 PRESENTATION
--
-- Preferred F1b API:
--   B1 selected source action = generated physical action
--   B2 operation/action application = exp(-source action)
--
-- The previous joint operationActionIsPhysicalTOperation equality is compiled.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FiniteDensityEvaluationExact as SourceEval
import DASHI.Physics.YangMills.BalabanCMP119PhysicalEffectiveActionRealizationExact as Generated
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

record BetaDrivenCMP119GeneratedActionFiniteVolumeInputs
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
    (generatedAction :
      Generated.CMP119PhysicalEffectiveActionRealization
        source family referenceInputs typed
        (SourceEval.asDownstreamAssemblySemantics sourceSemantics))
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    finiteVolumeExpectationIsGeneratedActionMixtureExpectation :
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
                (Generated.compilePhysicalTOperationAssemblyRealization
                  generatedAction)))
            cutoff))
        observable

open BetaDrivenCMP119GeneratedActionFiniteVolumeInputs public

asPreviousFiniteVolumeInputs :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics generatedAction thermodynamic} →
  BetaDrivenCMP119GeneratedActionFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics generatedAction thermodynamic →
  Previous.BetaDrivenCMP119PhysicalTOperationFiniteVolumeInputs
    source family referenceInputs typed sourceSemantics
    (Generated.compilePhysicalTOperationAssemblyRealization generatedAction)
    thermodynamic
asPreviousFiniteVolumeInputs inputs = record
  { finiteVolumeExpectationIsSourceFixedPhysicalTOperationExpectation =
      finiteVolumeExpectationIsGeneratedActionMixtureExpectation inputs
  }

compileBetaDrivenGeneratedActionRound283Presentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics generatedAction thermodynamic} →
  BetaDrivenCMP119GeneratedActionFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics generatedAction thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine SlowField thermodynamic
compileBetaDrivenGeneratedActionRound283Presentation inputs =
  Previous.compileBetaDrivenCMP119Round283Presentation
    (asPreviousFiniteVolumeInputs inputs)

compileBetaDrivenGeneratedActionSelectedT5ProbabilityPresentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics generatedAction thermodynamic} →
  BetaDrivenCMP119GeneratedActionFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics generatedAction thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine SlowField thermodynamic
compileBetaDrivenGeneratedActionSelectedT5ProbabilityPresentation inputs =
  Previous.compileBetaDrivenCMP119SelectedT5ProbabilityPresentation
    (asPreviousFiniteVolumeInputs inputs)

betaDrivenGeneratedActionRound283CompilerLevel : ProofLevel
betaDrivenGeneratedActionRound283CompilerLevel = machineChecked

betaDrivenGeneratedActionSelectedProbabilityCompilerLevel : ProofLevel
betaDrivenGeneratedActionSelectedProbabilityCompilerLevel = machineChecked

betaDrivenGeneratedActionToT5ExpectationSameObjectLevel : ProofLevel
betaDrivenGeneratedActionToT5ExpectationSameObjectLevel = conditional
