module DASHI.Physics.YangMills.BalabanClayGate4CanonicalFiniteRGReopeningExact where

------------------------------------------------------------------------
-- GATE4 NORMALIZED FINE LAW -> CANONICAL FINITE RG REOPENING STEP
--
-- FiniteRGReopeningStep had no physical constructor in the live repository.
-- This owner supplies the least-privilege constructor on the preferred Gate4
-- finite probability carrier.
--
-- The fine state list and fine weights are definitionally the selected Gate4
-- fast fibre and normalized reference selector.  The remaining physical RG
-- data are exactly the coarse law, fibre kernel/support and disintegration.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceToFiniteRGProbabilityExact as Gate4
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T

record CanonicalGate4ReopeningData
    {Scale Fine SlowField Component Functional Coarse : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}) : Set₁ where
  field
    scale : Scale
    component : Component
    slow : SlowField

    coarseStates : List Coarse
    project : Fine → Coarse
    coarseWeight : Coarse → ℚ
    reopeningKernel : Coarse → Fine → ℚ

    FibreSupport : Coarse → Fine → Set

    fibreSupportProjects : ∀ {coarse fine} →
      FibreSupport coarse fine → project fine ≡ coarse

    reopeningOffFibreZero : ∀ coarse fine →
      (FibreSupport coarse fine → ⊥) →
      reopeningKernel coarse fine ≡ Data.Rational.Base.0ℚ

    reopeningNormalized : ∀ coarse →
      Sums.sumRational
        (T.fastFibre
          (PhysicalT.canonicalPhysicalTData construction)
          scale component)
        (reopeningKernel coarse)
      ≡ Data.Rational.Base.1ℚ

    disintegrationExact : ∀ fine →
      Gate4.selectedReferenceProbabilityWeight
        (Preferred.compilePreferredRationalReferenceNormalization
          referenceInputs)
        scale component slow fine
      ≡
      Sums.sumRational coarseStates
        (λ coarse →
          coarseWeight coarse * reopeningKernel coarse fine)

open CanonicalGate4ReopeningData public

canonicalGate4ReopeningStep :
  ∀ {Scale Fine SlowField Component Functional Coarse}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}} →
  CanonicalGate4ReopeningData referenceInputs →
  Reopen.FiniteRGReopeningStep Fine Coarse
canonicalGate4ReopeningStep
  {construction = construction}
  {referenceInputs = referenceInputs}
  dataSet = record
  { fineStates =
      T.fastFibre
        (PhysicalT.canonicalPhysicalTData construction)
        (scale dataSet) (component dataSet)
  ; coarseStates = coarseStates dataSet
  ; project = project dataSet
  ; fineWeight =
      Gate4.selectedReferenceProbabilityWeight
        (Preferred.compilePreferredRationalReferenceNormalization
          referenceInputs)
        (scale dataSet) (component dataSet) (slow dataSet)
  ; coarseWeight = coarseWeight dataSet
  ; reopeningKernel = reopeningKernel dataSet
  ; FibreSupport = FibreSupport dataSet
  ; fibreSupportProjects = fibreSupportProjects dataSet
  ; reopeningOffFibreZero = reopeningOffFibreZero dataSet
  ; reopeningNormalized = reopeningNormalized dataSet
  ; disintegrationExact = disintegrationExact dataSet
  }

canonicalGate4ReopeningFineStates :
  ∀ {Scale Fine SlowField Component Functional Coarse}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    (dataSet : CanonicalGate4ReopeningData referenceInputs) →
  Reopen.fineStates (canonicalGate4ReopeningStep dataSet)
  ≡
  T.fastFibre
    (PhysicalT.canonicalPhysicalTData construction)
    (scale dataSet) (component dataSet)
canonicalGate4ReopeningFineStates dataSet = refl

canonicalGate4ReopeningFineWeight :
  ∀ {Scale Fine SlowField Component Functional Coarse}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    (dataSet : CanonicalGate4ReopeningData referenceInputs)
    fine →
  Reopen.fineWeight (canonicalGate4ReopeningStep dataSet) fine
  ≡
  Gate4.selectedReferenceProbabilityWeight
    (Preferred.compilePreferredRationalReferenceNormalization
      referenceInputs)
    (scale dataSet) (component dataSet) (slow dataSet) fine
canonicalGate4ReopeningFineWeight dataSet fine = refl

canonicalGate4ReopeningWeld :
  ∀ {Scale Fine SlowField Component Functional Coarse}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    (dataSet : CanonicalGate4ReopeningData referenceInputs) →
  Gate4.NormalizedReferenceReopeningWeld
    (Preferred.preferredRationalReferenceFoldSemantics referenceInputs)
    (canonicalGate4ReopeningStep dataSet)
canonicalGate4ReopeningWeld dataSet = record
  { scale = scale dataSet
  ; component = component dataSet
  ; slow = slow dataSet
  ; fineStatesAreSelectedFastFibre = refl
  ; fineWeightIsNormalizedReference = λ fine → refl
  }

canonicalGate4ReopeningProbabilityLaw :
  ∀ {Scale Fine SlowField Component Functional Coarse}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    (dataSet : CanonicalGate4ReopeningData referenceInputs) →
  DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact.FiniteRGProbabilityLaw
    (canonicalGate4ReopeningStep dataSet)
canonicalGate4ReopeningProbabilityLaw dataSet =
  Gate4.compileNormalizedReferenceProbabilityLaw
    (canonicalGate4ReopeningWeld dataSet)

canonicalGate4ReopeningCompilerLevel : ProofLevel
canonicalGate4ReopeningCompilerLevel = machineChecked

canonicalGate4ReopeningSameObjectWeldLevel : ProofLevel
canonicalGate4ReopeningSameObjectWeldLevel = machineChecked

canonicalGate4ReopeningProbabilityCompilerLevel : ProofLevel
canonicalGate4ReopeningProbabilityCompilerLevel = machineChecked

-- Genuine RG/physical input remaining in this constructor.
coarseLawAndFibreDisintegrationLevel : ProofLevel
coarseLawAndFibreDisintegrationLevel = conditional
