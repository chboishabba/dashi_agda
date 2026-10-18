module DASHI.Physics.YangMills.BalabanFiniteVolumeRawDensityGate4PresentationExact where

------------------------------------------------------------------------
-- CUTOFF-INDEXED RAW SLOW-FIELD DENSITY
--   -> CORRECTED CONDITIONAL GATE4 PRESENTATION
--
-- Raw finite slow-field density data are normalized exactly, then fed into the
-- constrained Gate4 conditional kernel.  Reopening steps and selected finite
-- probability laws are compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4RawSlowDensityToProbabilityExact as Raw
import DASHI.Physics.YangMills.BalabanFiniteVolumeConditionalGate4PresentationExact as Conditional
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Probability
import DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact as R283

record RawDensityGate4FiniteVolumePresentationInputs
    {Scale Fine SlowField Component Functional Measure : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    (typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    rawSlowDensityAt : Nat →
      Raw.Gate4RawSlowFieldDensity referenceInputs typed

    finiteVolumeExpectationIsRawDensityMixtureExpectation :
      ∀ cutoff observable →
      Gram.expectation (T5.operations thermodynamic)
        (Diagonal.selectedFiniteVolumeSequence thermodynamic cutoff)
        observable
      ≡
      Reopen.fineExpectation
        (Raw.compileRawSlowDensityReopeningStep
          (rawSlowDensityAt cutoff))
        observable

open RawDensityGate4FiniteVolumePresentationInputs public

asConditionalGate4FiniteVolumePresentation :
  ∀ {Scale Fine SlowField Component Functional Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ} →
  RawDensityGate4FiniteVolumePresentationInputs
    referenceInputs typed thermodynamic →
  Conditional.ConditionalGate4FiniteVolumePresentationInputs
    referenceInputs typed thermodynamic
asConditionalGate4FiniteVolumePresentation inputs = record
  { slowLawAt = λ cutoff →
      Raw.compileGate4SlowFieldProbabilityLaw
        (rawSlowDensityAt inputs cutoff)
  ; finiteVolumeExpectationIsConditionalMixtureExpectation =
      finiteVolumeExpectationIsRawDensityMixtureExpectation inputs
  }

compileRawDensityGate4Round283Presentation :
  ∀ {Scale Fine SlowField Component Functional Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ} →
  RawDensityGate4FiniteVolumePresentationInputs
    referenceInputs typed thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine SlowField thermodynamic
compileRawDensityGate4Round283Presentation inputs =
  Conditional.compileConditionalGate4Round283Presentation
    (asConditionalGate4FiniteVolumePresentation inputs)

compileRawDensityGate4SelectedT5ProbabilityPresentation :
  ∀ {Scale Fine SlowField Component Functional Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ} →
  RawDensityGate4FiniteVolumePresentationInputs
    referenceInputs typed thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine SlowField thermodynamic
compileRawDensityGate4SelectedT5ProbabilityPresentation inputs =
  Conditional.compileConditionalGate4SelectedT5ProbabilityPresentation
    (asConditionalGate4FiniteVolumePresentation inputs)

rawDensityGate4Round283CompilerLevel : ProofLevel
rawDensityGate4Round283CompilerLevel = machineChecked

rawDensityGate4SelectedProbabilityCompilerLevel : ProofLevel
rawDensityGate4SelectedProbabilityCompilerLevel = machineChecked

literalRawSlowDensityFamilyLevel : ProofLevel
literalRawSlowDensityFamilyLevel = conditional

finiteExpectationRawDensityMixtureSameObjectLevel : ProofLevel
finiteExpectationRawDensityMixtureSameObjectLevel = conditional
