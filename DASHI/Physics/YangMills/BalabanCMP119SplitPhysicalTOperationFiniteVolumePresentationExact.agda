module DASHI.Physics.YangMills.BalabanCMP119SplitPhysicalTOperationFiniteVolumePresentationExact where

------------------------------------------------------------------------
-- SPLIT CMP119 ASSEMBLY SEMANTICS + PHYSICAL T REALIZATION
--   -> FINITE T5 PRESENTATION
--
-- Downstream users no longer provide the old end-to-end
-- assembledDensityIsPhysicalTOperation field.  It is compiled internally from:
--
--   (A) evaluate(assembleDensity T A) = applyOperationAction T A
--   (B) selected applyOperationAction(T_k,A_k)
--         = physical localized T-operation at one.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact as Assembly
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationAssemblyRealizationExact as Realization
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationFiniteVolumePresentationExact as Previous
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

record CMP119SplitPhysicalTOperationFiniteVolumeInputs
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
    (semantics :
      Assembly.CMP119FiniteDensityAssemblySemantics
        source family SlowField)
    (realization :
      Realization.CMP119PhysicalTOperationAssemblyRealization
        source family referenceInputs typed semantics)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    finiteVolumeExpectationIsSplitPhysicalTOperationMixtureExpectation :
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

open CMP119SplitPhysicalTOperationFiniteVolumeInputs public

asPreviousPhysicalTOperationFiniteVolumeInputs :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed semantics realization thermodynamic} →
  CMP119SplitPhysicalTOperationFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed semantics realization thermodynamic →
  Previous.CMP119PhysicalTOperationFiniteVolumeInputs
    source family referenceInputs typed
    (Assembly.asAssembledDensityFiniteEvaluator semantics)
    (Realization.compileEndToEndPhysicalTOperationWeld realization)
    thermodynamic
asPreviousPhysicalTOperationFiniteVolumeInputs inputs = record
  { finiteVolumeExpectationIsPhysicalTOperationMixtureExpectation =
      finiteVolumeExpectationIsSplitPhysicalTOperationMixtureExpectation inputs
  }

compileCMP119SplitPhysicalTOperationRound283Presentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed semantics realization thermodynamic} →
  CMP119SplitPhysicalTOperationFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed semantics realization thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine SlowField thermodynamic
compileCMP119SplitPhysicalTOperationRound283Presentation inputs =
  Previous.compileCMP119PhysicalTOperationRound283Presentation
    (asPreviousPhysicalTOperationFiniteVolumeInputs inputs)

compileCMP119SplitPhysicalTOperationSelectedT5ProbabilityPresentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed semantics realization thermodynamic} →
  CMP119SplitPhysicalTOperationFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed semantics realization thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine SlowField thermodynamic
compileCMP119SplitPhysicalTOperationSelectedT5ProbabilityPresentation inputs =
  Previous.compileCMP119PhysicalTOperationSelectedT5ProbabilityPresentation
    (asPreviousPhysicalTOperationFiniteVolumeInputs inputs)

cmp119SplitPhysicalTOperationRound283CompilerLevel : ProofLevel
cmp119SplitPhysicalTOperationRound283CompilerLevel = machineChecked

cmp119SplitPhysicalTOperationSelectedProbabilityCompilerLevel : ProofLevel
cmp119SplitPhysicalTOperationSelectedProbabilityCompilerLevel = machineChecked

cmp119SplitPhysicalTOperationT5ExpectationSameObjectLevel : ProofLevel
cmp119SplitPhysicalTOperationT5ExpectationSameObjectLevel = conditional
