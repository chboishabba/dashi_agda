module DASHI.Physics.YangMills.BalabanCMP119Gate4ConstrainedMassFiniteVolumePresentationExact where

------------------------------------------------------------------------
-- CMP119 = GATE4 CONSTRAINED MASS
--   -> FINITE POSITIVE LAW -> ROUND283 PRESENTATION
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteSlowDensityExact as Assembled
import DASHI.Physics.YangMills.BalabanCMP119Gate4ConstrainedMassWeldExact as Weld
import DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteVolumeGate4PresentationExact as Presentation
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

record CMP119ConstrainedMassFiniteVolumeInputs
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
      Assembled.CMP119AssembledDensityFiniteEvaluator family SlowField)
    (weld :
      Weld.CMP119Gate4ConstrainedMassWeld
        source family referenceInputs typed evaluator)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    finiteVolumeExpectationIsConstrainedMassMixtureExpectation :
      ∀ cutoff observable →
      Gram.expectation (T5.operations thermodynamic)
        (Diagonal.selectedFiniteVolumeSequence thermodynamic cutoff)
        observable
      ≡
      Reopen.fineExpectation
        (Raw.compileRawSlowDensityReopeningStep
          (Assembled.compileAssembledSelectedDensityRawSlowLaw
            (Weld.compileCMP119AssembledFiniteSlowDensityRealization weld)
            cutoff))
        observable

open CMP119ConstrainedMassFiniteVolumeInputs public

asAssembledFiniteVolumePresentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed evaluator weld thermodynamic} →
  CMP119ConstrainedMassFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed evaluator weld thermodynamic →
  Presentation.CMP119AssembledGate4FiniteVolumePresentationInputs
    source family referenceInputs typed evaluator
    (Weld.compileCMP119AssembledFiniteSlowDensityRealization weld)
    thermodynamic
asAssembledFiniteVolumePresentation inputs = record
  { finiteVolumeExpectationIsAssembledCMP119MixtureExpectation =
      finiteVolumeExpectationIsConstrainedMassMixtureExpectation inputs
  }

compileCMP119ConstrainedMassRound283Presentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed evaluator weld thermodynamic} →
  CMP119ConstrainedMassFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed evaluator weld thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine SlowField thermodynamic
compileCMP119ConstrainedMassRound283Presentation inputs =
  Presentation.compileCMP119AssembledGate4Round283Presentation
    (asAssembledFiniteVolumePresentation inputs)

compileCMP119ConstrainedMassSelectedT5ProbabilityPresentation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed evaluator weld thermodynamic} →
  CMP119ConstrainedMassFiniteVolumeInputs
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed evaluator weld thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine SlowField thermodynamic
compileCMP119ConstrainedMassSelectedT5ProbabilityPresentation inputs =
  Presentation.compileCMP119AssembledGate4SelectedT5ProbabilityPresentation
    (asAssembledFiniteVolumePresentation inputs)

cmp119ConstrainedMassRound283CompilerLevel : ProofLevel
cmp119ConstrainedMassRound283CompilerLevel = machineChecked

cmp119ConstrainedMassSelectedProbabilityCompilerLevel : ProofLevel
cmp119ConstrainedMassSelectedProbabilityCompilerLevel = machineChecked

cmp119ConstrainedMassToT5ExpectationSameObjectLevel : ProofLevel
cmp119ConstrainedMassToT5ExpectationSameObjectLevel = conditional
