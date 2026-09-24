module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Round214GeneratedActionFiniteVolumeExact where

------------------------------------------------------------------------
-- SOURCE-FIXED CMP119 DENSITY + ROUND214 ACTION SEMANTICS
--   -> GENERATED PHYSICAL ACTION -> FINITE T5 PRESENTATION
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FiniteDensityEvaluationExact as SourceEval
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Round214ActionEvaluationExact as R214Action
import DASHI.Physics.YangMills.BalabanCMP119Round214BackedPhysicalEffectiveActionExact as R214Generated
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119GeneratedActionFiniteVolumeExact as Previous
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
import DASHI.Physics.YangMills.BalabanCMP119PhysicalEffectiveActionRealizationExact as Generated

record BetaDrivenCMP119Round214GeneratedActionFiniteVolumeInputs
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
    (round214 :
      R214Action.BetaDrivenCMP119Round214ActionEvaluation
        source family)
    (round214Generated :
      R214Generated.CMP119Round214BackedPhysicalEffectiveAction
        source family referenceInputs typed
        (SourceEval.asDownstreamAssemblySemantics sourceSemantics)
        round214)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    finiteVolumeExpectationIsRound214GeneratedActionMixtureExpectation :
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
                  (R214Generated.compilePhysicalEffectiveActionRealization
                    round214Generated))))
            cutoff))
        observable

open BetaDrivenCMP119Round214GeneratedActionFiniteVolumeInputs public

asPreviousGeneratedActionFiniteVolumeInputs :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics round214
      round214Generated thermodynamic} →
  BetaDrivenCMP119Round214GeneratedActionFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics round214
    round214Generated thermodynamic →
  Previous.BetaDrivenCMP119GeneratedActionFiniteVolumeInputs
    source family referenceInputs typed sourceSemantics
    (R214Generated.compilePhysicalEffectiveActionRealization round214Generated)
    thermodynamic
asPreviousGeneratedActionFiniteVolumeInputs inputs = record
  { finiteVolumeExpectationIsGeneratedActionMixtureExpectation =
      finiteVolumeExpectationIsRound214GeneratedActionMixtureExpectation inputs
  }

compileBetaDrivenRound214GeneratedActionRound283Presentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics round214
      round214Generated thermodynamic} →
  BetaDrivenCMP119Round214GeneratedActionFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics round214
    round214Generated thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine SlowField thermodynamic
compileBetaDrivenRound214GeneratedActionRound283Presentation inputs =
  Previous.compileBetaDrivenGeneratedActionRound283Presentation
    (asPreviousGeneratedActionFiniteVolumeInputs inputs)

compileBetaDrivenRound214GeneratedActionSelectedT5ProbabilityPresentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics round214
      round214Generated thermodynamic} →
  BetaDrivenCMP119Round214GeneratedActionFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics round214
    round214Generated thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine SlowField thermodynamic
compileBetaDrivenRound214GeneratedActionSelectedT5ProbabilityPresentation inputs =
  Previous.compileBetaDrivenGeneratedActionSelectedT5ProbabilityPresentation
    (asPreviousGeneratedActionFiniteVolumeInputs inputs)

betaDrivenRound214GeneratedActionRound283CompilerLevel : ProofLevel
betaDrivenRound214GeneratedActionRound283CompilerLevel = machineChecked

betaDrivenRound214GeneratedActionSelectedProbabilityCompilerLevel : ProofLevel
betaDrivenRound214GeneratedActionSelectedProbabilityCompilerLevel = machineChecked

betaDrivenRound214GeneratedActionToT5ExpectationSameObjectLevel : ProofLevel
betaDrivenRound214GeneratedActionToT5ExpectationSameObjectLevel = conditional
