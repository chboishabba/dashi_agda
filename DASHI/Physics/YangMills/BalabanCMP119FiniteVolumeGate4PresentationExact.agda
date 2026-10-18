module DASHI.Physics.YangMills.BalabanCMP119FiniteVolumeGate4PresentationExact where

------------------------------------------------------------------------
-- SELECTED CMP119 DENSITY -> CORRECTED GATE4 ROUND283 PRESENTATION
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as CMP119
import DASHI.Physics.YangMills.BalabanCMP119FiniteSlowDensityRealizationExact as Density
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4RawSlowDensityToProbabilityExact as Raw
import DASHI.Physics.YangMills.BalabanFiniteVolumeRawDensityGate4PresentationExact as RawPresentation
import DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact as R283
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Probability
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal

record CMP119Gate4FiniteVolumePresentationInputs
    {trajectory split}
    (source :
      CMP119.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split})
    {Scale Fine SlowField Component Functional Measure : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    (typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs)
    (densityRealization :
      Density.CMP119FiniteSlowDensityRealization
        source referenceInputs typed)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    finiteVolumeExpectationIsCMP119MixtureExpectation :
      ∀ cutoff observable →
      Gram.expectation (T5.operations thermodynamic)
        (Diagonal.selectedFiniteVolumeSequence thermodynamic cutoff)
        observable
      ≡
      Reopen.fineExpectation
        (Raw.compileRawSlowDensityReopeningStep
          (Density.compileSelectedDensityRawSlowLaw
            densityRealization cutoff))
        observable

open CMP119Gate4FiniteVolumePresentationInputs public

asRawDensityGate4Presentation :
  ∀ {trajectory split source
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed densityRealization thermodynamic} →
  CMP119Gate4FiniteVolumePresentationInputs
    {trajectory = trajectory} {split = split}
    source
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed densityRealization thermodynamic →
  RawPresentation.RawDensityGate4FiniteVolumePresentationInputs
    referenceInputs typed thermodynamic
asRawDensityGate4Presentation
  {densityRealization = densityRealization} inputs = record
  { rawSlowDensityAt =
      Density.compileSelectedDensityRawSlowLaw densityRealization
  ; finiteVolumeExpectationIsRawDensityMixtureExpectation =
      finiteVolumeExpectationIsCMP119MixtureExpectation inputs
  }

compileCMP119Gate4Round283Presentation :
  ∀ {trajectory split source
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed densityRealization thermodynamic} →
  CMP119Gate4FiniteVolumePresentationInputs
    {trajectory = trajectory} {split = split}
    source
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed densityRealization thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine SlowField thermodynamic
compileCMP119Gate4Round283Presentation inputs =
  RawPresentation.compileRawDensityGate4Round283Presentation
    (asRawDensityGate4Presentation inputs)

compileCMP119Gate4SelectedT5ProbabilityPresentation :
  ∀ {trajectory split source
      Scale Fine SlowField Component Functional Measure
      construction referenceInputs typed densityRealization thermodynamic} →
  CMP119Gate4FiniteVolumePresentationInputs
    {trajectory = trajectory} {split = split}
    source
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {Measure = Measure}
    {construction = construction}
    referenceInputs typed densityRealization thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine SlowField thermodynamic
compileCMP119Gate4SelectedT5ProbabilityPresentation inputs =
  RawPresentation.compileRawDensityGate4SelectedT5ProbabilityPresentation
    (asRawDensityGate4Presentation inputs)

cmp119Gate4Round283CompilerLevel : ProofLevel
cmp119Gate4Round283CompilerLevel = machineChecked

cmp119Gate4SelectedProbabilityCompilerLevel : ProofLevel
cmp119Gate4SelectedProbabilityCompilerLevel = machineChecked

cmp119ToT5FiniteExpectationSameObjectLevel : ProofLevel
cmp119ToT5FiniteExpectationSameObjectLevel = conditional
