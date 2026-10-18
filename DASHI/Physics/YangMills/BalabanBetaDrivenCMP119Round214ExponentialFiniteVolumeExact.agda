module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Round214ExponentialFiniteVolumeExact where

------------------------------------------------------------------------
-- SOURCE-FIXED CMP119 + ROUND214 EXPONENTIAL PHYSICAL-T BRIDGE
--   -> FINITE T5 PRESENTATION
--
-- This is the preferred log-free finite source path.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FiniteDensityEvaluationExact as SourceEval
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Round214ActionEvaluationExact as R214Action
import DASHI.Physics.YangMills.BalabanCMP119Round214ExponentialPhysicalTBridgeExact as Bridge
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

record BetaDrivenCMP119Round214ExponentialFiniteVolumeInputs
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
    (bridge :
      Bridge.CMP119Round214ExponentialPhysicalTBridge
        source family referenceInputs typed
        (SourceEval.asDownstreamAssemblySemantics sourceSemantics)
        round214)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    finiteVolumeExpectationIsRound214ExponentialMixtureExpectation :
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
                (Bridge.compilePhysicalTOperationAssemblyRealization bridge)))
            cutoff))
        observable

open BetaDrivenCMP119Round214ExponentialFiniteVolumeInputs public

asPreviousFiniteVolumeInputs :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics round214
      bridge thermodynamic} →
  BetaDrivenCMP119Round214ExponentialFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics round214 bridge thermodynamic →
  Previous.BetaDrivenCMP119PhysicalTOperationFiniteVolumeInputs
    source family referenceInputs typed sourceSemantics
    (Bridge.compilePhysicalTOperationAssemblyRealization bridge)
    thermodynamic
asPreviousFiniteVolumeInputs inputs = record
  { finiteVolumeExpectationIsSourceFixedPhysicalTOperationExpectation =
      finiteVolumeExpectationIsRound214ExponentialMixtureExpectation inputs
  }

compileBetaDrivenRound214ExponentialRound283Presentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics round214
      bridge thermodynamic} →
  BetaDrivenCMP119Round214ExponentialFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics round214 bridge thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine SlowField thermodynamic
compileBetaDrivenRound214ExponentialRound283Presentation inputs =
  Previous.compileBetaDrivenCMP119Round283Presentation
    (asPreviousFiniteVolumeInputs inputs)

compileBetaDrivenRound214ExponentialSelectedT5ProbabilityPresentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed sourceSemantics round214
      bridge thermodynamic} →
  BetaDrivenCMP119Round214ExponentialFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed sourceSemantics round214 bridge thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine SlowField thermodynamic
compileBetaDrivenRound214ExponentialSelectedT5ProbabilityPresentation inputs =
  Previous.compileBetaDrivenCMP119SelectedT5ProbabilityPresentation
    (asPreviousFiniteVolumeInputs inputs)

betaDrivenRound214ExponentialRound283CompilerLevel : ProofLevel
betaDrivenRound214ExponentialRound283CompilerLevel = machineChecked

betaDrivenRound214ExponentialSelectedProbabilityCompilerLevel : ProofLevel
betaDrivenRound214ExponentialSelectedProbabilityCompilerLevel = machineChecked

betaDrivenRound214ExponentialToT5ExpectationSameObjectLevel : ProofLevel
betaDrivenRound214ExponentialToT5ExpectationSameObjectLevel = conditional
