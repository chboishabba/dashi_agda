module DASHI.Physics.YangMills.BalabanClayGate4PhysicalReferenceMassAssemblyExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass

------------------------------------------------------------------------
-- Primary provenance.
--
-- André Weil, "L'intégration dans les groupes topologiques et ses
-- applications", Hermann, Paris (1940). No DOI assigned.
--
-- Gerald B. Folland, "A Course in Abstract Harmonic Analysis", second
-- edition, CRC Press (2016). DOI: 10.1201/b19172.
--
-- This module uses only the finite selected-fibre consequence: one strictly
-- positive selected configuration and nonnegative remaining weights imply a
-- positive normalizing mass.  The physical construction of that configuration
-- remains explicit rather than being replaced by a general Haar slogan.
------------------------------------------------------------------------

record PhysicalPositiveReferenceConstruction
    {Scale Fine SlowField Component Functional Scalar : Set}
    (dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    referenceAlgebra :
      Reference.FiniteReferenceFibreAlgebra (T.sumData dataSet)
    positiveAlgebra :
      PositiveMass.PositiveFiniteFoldAlgebra (T.sumData dataSet)
    reciprocalAlgebra :
      PositiveMass.PositiveMassReciprocalAlgebra
        referenceAlgebra positiveAlgebra

    rawSelectedReference : Scale → Component → SlowField → Fine → Scalar

    positiveSelectedFibre : ∀ scale component slow →
      PositiveMass.PositiveSelectedReferenceFibre
        positiveAlgebra
        (rawSelectedReference scale component slow)
        slow
        (T.fastFibre dataSet scale component)

    suppression : Scale → Scalar
    referenceIntegrand : Scale → Component → SlowField → Fine → Scalar

    selectedReferenceIntegrandMeaning :
      ∀ scale component slow fine →
      Integral.selectedWith (T.sumData dataSet)
        (referenceIntegrand scale component slow) slow fine
      ≡ Reference.scaledSelector referenceAlgebra (suppression scale)
          (Reference.normalizedReferenceSelector
            (PositiveMass.reciprocalReferenceMassFromPositiveWitness
              reciprocalAlgebra
              (positiveSelectedFibre scale component slow))) fine

open PhysicalPositiveReferenceConstruction public

asTReferenceReciprocalConstruction :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar} →
  PhysicalPositiveReferenceConstruction dataSet →
  Reference.TReferenceReciprocalConstruction dataSet
asTReferenceReciprocalConstruction construction = record
  { Reference.TReferenceReciprocalConstruction.algebra =
      referenceAlgebra construction
  ; Reference.TReferenceReciprocalConstruction.rawSelectedReference =
      rawSelectedReference construction
  ; Reference.TReferenceReciprocalConstruction.reciprocalReference =
      λ scale component slow →
        PositiveMass.reciprocalReferenceMassFromPositiveWitness
          (reciprocalAlgebra construction)
          (positiveSelectedFibre construction scale component slow)
  ; Reference.TReferenceReciprocalConstruction.suppression =
      suppression construction
  ; Reference.TReferenceReciprocalConstruction.referenceIntegrand =
      referenceIntegrand construction
  ; Reference.TReferenceReciprocalConstruction.selectedReferenceIntegrandMeaning =
      selectedReferenceIntegrandMeaning construction
  }

physicalReferenceNormalization :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar} →
  PhysicalPositiveReferenceConstruction dataSet →
  Reference.TReferenceFibreNormalization dataSet
physicalReferenceNormalization construction =
  Reference.tReferenceNormalizationFromReciprocal
    (asTReferenceReciprocalConstruction construction)

physicalPositiveReferenceAssemblyLevel : ProofLevel
physicalPositiveReferenceAssemblyLevel = machineChecked

physicalReferenceNormalizationFromPositiveWitnessLevel : ProofLevel
physicalReferenceNormalizationFromPositiveWitnessLevel = machineChecked

physicalReferenceIdentityConfigurationInputsLevel : ProofLevel
physicalReferenceIdentityConfigurationInputsLevel = conditional

physicalReferenceWeightStrictPositivityInputsLevel : ProofLevel
physicalReferenceWeightStrictPositivityInputsLevel = conditional

physicalReferenceScalarReciprocalInputsLevel : ProofLevel
physicalReferenceScalarReciprocalInputsLevel = conditional
