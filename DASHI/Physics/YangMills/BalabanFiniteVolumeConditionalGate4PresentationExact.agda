module DASHI.Physics.YangMills.BalabanFiniteVolumeConditionalGate4PresentationExact where

------------------------------------------------------------------------
-- CUTOFF-INDEXED SLOW-FIELD LAW + GATE4 CONDITIONAL KERNEL
--   -> ROUND283 PRESENTATION / SELECTED PROBABILITY FAMILY
--
-- This is the corrected preferred finite semantic route.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Probability
import DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact as R283
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4ConditionalMixtureReopeningExact as Mixture

record ConditionalGate4FiniteVolumePresentationInputs
    {Scale Fine SlowField Component Functional Measure : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    (typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    slowLawAt : Nat →
      Mixture.Gate4SlowFieldProbabilityLaw referenceInputs typed

    finiteVolumeExpectationIsConditionalMixtureExpectation :
      ∀ cutoff observable →
      Gram.expectation (T5.operations thermodynamic)
        (Diagonal.selectedFiniteVolumeSequence thermodynamic cutoff)
        observable
      ≡
      Reopen.fineExpectation
        (Mixture.gate4ConditionalMixtureReopeningStep
          (slowLawAt cutoff))
        observable

open ConditionalGate4FiniteVolumePresentationInputs public

compileConditionalGate4Round283Presentation :
  ∀ {Scale Fine SlowField Component Functional Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ} →
  ConditionalGate4FiniteVolumePresentationInputs
    referenceInputs typed thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine SlowField thermodynamic
compileConditionalGate4Round283Presentation inputs = record
  { stepAt = λ cutoff →
      Mixture.gate4ConditionalMixtureReopeningStep
        (slowLawAt inputs cutoff)
  ; finiteVolumeExpectationIsReopeningExpectation =
      finiteVolumeExpectationIsConditionalMixtureExpectation inputs
  }

compileConditionalGate4SelectedT5ProbabilityPresentation :
  ∀ {Scale Fine SlowField Component Functional Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ} →
  ConditionalGate4FiniteVolumePresentationInputs
    referenceInputs typed thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine SlowField thermodynamic
compileConditionalGate4SelectedT5ProbabilityPresentation inputs = record
  { presentation =
      compileConditionalGate4Round283Presentation inputs
  ; probabilityAt = λ cutoff →
      Mixture.gate4ConditionalMixtureFineProbabilityLaw
        (slowLawAt inputs cutoff)
  }

conditionalGate4Round283CompilerLevel : ProofLevel
conditionalGate4Round283CompilerLevel = machineChecked

conditionalGate4SelectedProbabilityCompilerLevel : ProofLevel
conditionalGate4SelectedProbabilityCompilerLevel = machineChecked

physicalSlowFieldLawFamilyLevel : ProofLevel
physicalSlowFieldLawFamilyLevel = conditional

finiteExpectationConditionalMixtureSameObjectLevel : ProofLevel
finiteExpectationConditionalMixtureSameObjectLevel = conditional
