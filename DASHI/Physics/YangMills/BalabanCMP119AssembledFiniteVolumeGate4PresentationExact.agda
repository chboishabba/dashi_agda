module DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteVolumeGate4PresentationExact where

------------------------------------------------------------------------
-- ASSEMBLED CMP119 DENSITY -> CORRECTED GATE4 ROUND283 PRESENTATION
--
-- This is the source-pinned variant of the older
-- CMP119FiniteVolumeGate4PresentationExact route.  The raw slow-field law is
-- obtained from the exact Round219 (T_k,A_k) assembled density coordinates,
-- never from an arbitrary total Density interpreter.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteSlowDensityExact as Density
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanFiniteVolumeRawDensityGate4PresentationExact as RawPresentation
import DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact as R283
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Probability
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayGate4RawSlowDensityToProbabilityExact as Raw

record CMP119AssembledGate4FiniteVolumePresentationInputs
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
    (evaluator :
      Density.CMP119AssembledDensityFiniteEvaluator family SlowField)
    (densityRealization :
      Density.CMP119AssembledFiniteSlowDensityRealization
        source family referenceInputs typed evaluator)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    finiteVolumeExpectationIsAssembledCMP119MixtureExpectation :
      ∀ cutoff observable →
      Gram.expectation (T5.operations thermodynamic)
        (Diagonal.selectedFiniteVolumeSequence thermodynamic cutoff)
        observable
      ≡
      Reopen.fineExpectation
        (Raw.compileRawSlowDensityReopeningStep
          (Density.compileAssembledSelectedDensityRawSlowLaw
            densityRealization cutoff))
        observable

open CMP119AssembledGate4FiniteVolumePresentationInputs public

asRawDensityGate4Presentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed evaluator
      densityRealization thermodynamic} →
  CMP119AssembledGate4FiniteVolumePresentationInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed evaluator densityRealization thermodynamic →
  RawPresentation.RawDensityGate4FiniteVolumePresentationInputs
    referenceInputs typed thermodynamic
asRawDensityGate4Presentation
  {densityRealization = densityRealization} inputs = record
  { rawSlowDensityAt =
      Density.compileAssembledSelectedDensityRawSlowLaw densityRealization
  ; finiteVolumeExpectationIsRawDensityMixtureExpectation =
      finiteVolumeExpectationIsAssembledCMP119MixtureExpectation inputs
  }

compileCMP119AssembledGate4Round283Presentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed evaluator
      densityRealization thermodynamic} →
  CMP119AssembledGate4FiniteVolumePresentationInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed evaluator densityRealization thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine SlowField thermodynamic
compileCMP119AssembledGate4Round283Presentation inputs =
  RawPresentation.compileRawDensityGate4Round283Presentation
    (asRawDensityGate4Presentation inputs)

compileCMP119AssembledGate4SelectedT5ProbabilityPresentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed evaluator
      densityRealization thermodynamic} →
  CMP119AssembledGate4FiniteVolumePresentationInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed evaluator densityRealization thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine SlowField thermodynamic
compileCMP119AssembledGate4SelectedT5ProbabilityPresentation inputs =
  RawPresentation.compileRawDensityGate4SelectedT5ProbabilityPresentation
    (asRawDensityGate4Presentation inputs)

cmp119AssembledGate4Round283CompilerLevel : ProofLevel
cmp119AssembledGate4Round283CompilerLevel = machineChecked

cmp119AssembledGate4SelectedProbabilityCompilerLevel : ProofLevel
cmp119AssembledGate4SelectedProbabilityCompilerLevel = machineChecked

-- Surviving finite semantic weld: the selected T5 expectation must be shown
-- to be the expectation of this exact source-assembled finite law.
cmp119AssembledToT5FiniteExpectationSameObjectLevel : ProofLevel
cmp119AssembledToT5FiniteExpectationSameObjectLevel = conditional
