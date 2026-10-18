module DASHI.Physics.YangMills.BalabanFiniteVolumeCanonicalGate4PresentationExact where

------------------------------------------------------------------------
-- CANONICAL GATE4 REOPENING FAMILY -> ROUND283 PRESENTATION
--
-- Earlier Round283 accepted an arbitrary stepAt and a same-object expectation
-- identity.  The preferred Gate4 route now constructs each reopening step from
-- the normalized Gate4 finite probability law and the physical coarse/fibre
-- disintegration data.
--
-- Consequently:
--   * stepAt is compiler-owned;
--   * fineStates/fineWeight same-object equalities are definitional;
--   * the selected T5 finite probability presentation is compiler-owned.
--
-- The only Round283 physical/provenance payment left here is the expectation
-- identity for the exact constructed reopening step.
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
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalFiniteRGReopeningExact as Canonical

record CanonicalGate4FiniteVolumePresentationInputs
    {Scale Fine SlowField Component Functional Coarse Measure : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    reopeningDataAt : Nat →
      Canonical.CanonicalGate4ReopeningData referenceInputs

    finiteVolumeExpectationIsCanonicalReopeningExpectation :
      ∀ cutoff observable →
      Gram.expectation (T5.operations thermodynamic)
        (Diagonal.selectedFiniteVolumeSequence thermodynamic cutoff)
        observable
      ≡
      Reopen.fineExpectation
        (Canonical.canonicalGate4ReopeningStep
          (reopeningDataAt cutoff))
        observable

open CanonicalGate4FiniteVolumePresentationInputs public

compileCanonicalGate4Round283Presentation :
  ∀ {Scale Fine SlowField Component Functional Coarse Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ} →
  CanonicalGate4FiniteVolumePresentationInputs
    referenceInputs thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine Coarse thermodynamic
compileCanonicalGate4Round283Presentation inputs = record
  { stepAt = λ cutoff →
      Canonical.canonicalGate4ReopeningStep
        (reopeningDataAt inputs cutoff)
  ; finiteVolumeExpectationIsReopeningExpectation =
      finiteVolumeExpectationIsCanonicalReopeningExpectation inputs
  }

compileCanonicalGate4SelectedT5ProbabilityPresentation :
  ∀ {Scale Fine SlowField Component Functional Coarse Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ} →
  CanonicalGate4FiniteVolumePresentationInputs
    referenceInputs thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine Coarse thermodynamic
compileCanonicalGate4SelectedT5ProbabilityPresentation inputs = record
  { presentation =
      compileCanonicalGate4Round283Presentation inputs
  ; probabilityAt = λ cutoff →
      Canonical.canonicalGate4ReopeningProbabilityLaw
        (reopeningDataAt inputs cutoff)
  }

canonicalGate4Round283StepCompilerLevel : ProofLevel
canonicalGate4Round283StepCompilerLevel = machineChecked

canonicalGate4SelectedProbabilityFamilyCompilerLevel : ProofLevel
canonicalGate4SelectedProbabilityFamilyCompilerLevel = machineChecked

-- The exact finite T5 expectation must still be identified with the constructed
-- weighted reopening law.  This is the surviving Round283 same-object payment.
finiteVolumeExpectationCanonicalReopeningSameObjectLevel : ProofLevel
finiteVolumeExpectationCanonicalReopeningSameObjectLevel = conditional

-- The coarse/fibre disintegration data remain the genuine finite RG input.
finiteRGCoarseFibreDisintegrationLevel : ProofLevel
finiteRGCoarseFibreDisintegrationLevel = conditional
