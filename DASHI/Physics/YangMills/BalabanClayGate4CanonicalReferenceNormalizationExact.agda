module DASHI.Physics.YangMills.BalabanClayGate4CanonicalReferenceNormalizationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass
import DASHI.Physics.YangMills.BalabanClayGate4FlatReferencePositiveWitnessExact as Flat
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalReferenceFactorAssemblyExact as Canonical
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalReferenceMassAssemblyExact as Physical

------------------------------------------------------------------------
-- Provenance.
--
-- André Weil,
-- "L'intégration dans les groupes topologiques et ses applications",
-- Hermann, Paris (1940). No DOI assigned.
--
-- Gerald B. Folland,
-- "A Course in Abstract Harmonic Analysis", second edition,
-- CRC Press (2016). DOI: 10.1201/b19172.
--
-- This is the end-to-end finite reference constructor. The physical background,
-- factor and selector meanings remain visible inputs; finite positivity,
-- rational reciprocal normalization and the T-reference package are derived.
------------------------------------------------------------------------

record CanonicalRationalReferenceNormalizationData
    (Scale Fine SlowField Component Functional : Set)
    (tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ) : Set₁ where
  field
    referenceAlgebra :
      Reference.FiniteReferenceFibreAlgebra (T.sumData tData)
    positiveAlgebra :
      PositiveMass.PositiveFiniteFoldAlgebra (T.sumData tData)

    factors : Flat.FlatReferenceFactorData tData positiveAlgebra

    rationalInterpretation :
      Reciprocal.RationalPositiveMassInterpretation
        referenceAlgebra positiveAlgebra

    canonicalReferenceInputs : ∀ scale component slow →
      Canonical.CanonicalReferenceFactorInputs
        factors scale component slow

    suppression : Scale → ℚ
    referenceIntegrand : Scale → Component → SlowField → Fine → ℚ

    selectedReferenceIntegrandMeaning :
      ∀ scale component slow fine →
      Integral.selectedWith (T.sumData tData)
        (referenceIntegrand scale component slow) slow fine
      ≡ Reference.scaledSelector referenceAlgebra (suppression scale)
          (Reference.normalizedReferenceSelector
            (PositiveMass.reciprocalReferenceMassFromPositiveWitness
              (Reciprocal.rationalPositiveMassReciprocalAlgebra
                rationalInterpretation)
              (Flat.positiveSelectedReferenceFibreFromFlat
                (Canonical.asFlatReferenceInPhysicalFibre
                  (canonicalReferenceInputs scale component slow))))) fine

open CanonicalRationalReferenceNormalizationData public

positiveSelectedFibre :
  ∀ {Scale Fine SlowField Component Functional}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ} →
  (dataSet : CanonicalRationalReferenceNormalizationData
    Scale Fine SlowField Component Functional tData) →
  ∀ scale component slow →
  PositiveMass.PositiveSelectedReferenceFibre
    (positiveAlgebra dataSet)
    (Flat.rawSelectedReference (factors dataSet) scale component slow)
    slow
    (T.fastFibre tData scale component)
positiveSelectedFibre dataSet scale component slow =
  Flat.positiveSelectedReferenceFibreFromFlat
    (Canonical.asFlatReferenceInPhysicalFibre
      (canonicalReferenceInputs dataSet scale component slow))

asPhysicalPositiveReferenceConstruction :
  ∀ {Scale Fine SlowField Component Functional}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ} →
  CanonicalRationalReferenceNormalizationData
    Scale Fine SlowField Component Functional tData →
  Physical.PhysicalPositiveReferenceConstruction tData
asPhysicalPositiveReferenceConstruction dataSet = record
  { Physical.PhysicalPositiveReferenceConstruction.referenceAlgebra =
      referenceAlgebra dataSet
  ; Physical.PhysicalPositiveReferenceConstruction.positiveAlgebra =
      positiveAlgebra dataSet
  ; Physical.PhysicalPositiveReferenceConstruction.reciprocalAlgebra =
      Reciprocal.rationalPositiveMassReciprocalAlgebra
        (rationalInterpretation dataSet)
  ; Physical.PhysicalPositiveReferenceConstruction.rawSelectedReference =
      Flat.rawSelectedReference (factors dataSet)
  ; Physical.PhysicalPositiveReferenceConstruction.positiveSelectedFibre =
      positiveSelectedFibre dataSet
  ; Physical.PhysicalPositiveReferenceConstruction.suppression =
      suppression dataSet
  ; Physical.PhysicalPositiveReferenceConstruction.referenceIntegrand =
      referenceIntegrand dataSet
  ; Physical.PhysicalPositiveReferenceConstruction.selectedReferenceIntegrandMeaning =
      selectedReferenceIntegrandMeaning dataSet
  }

canonicalPhysicalReferenceNormalization :
  ∀ {Scale Fine SlowField Component Functional}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ} →
  CanonicalRationalReferenceNormalizationData
    Scale Fine SlowField Component Functional tData →
  Reference.TReferenceFibreNormalization tData
canonicalPhysicalReferenceNormalization dataSet =
  Physical.physicalReferenceNormalization
    (asPhysicalPositiveReferenceConstruction dataSet)

canonicalReferencePositiveFibreAssemblyLevel : ProofLevel
canonicalReferencePositiveFibreAssemblyLevel = machineChecked

canonicalRationalReferenceConstructionLevel : ProofLevel
canonicalRationalReferenceConstructionLevel = machineChecked

canonicalPhysicalReferenceNormalizationLevel : ProofLevel
canonicalPhysicalReferenceNormalizationLevel = machineChecked

physicalCanonicalReferenceFamilyInputsLevel : ProofLevel
physicalCanonicalReferenceFamilyInputsLevel = conditional

physicalSelectedReferenceIntegrandMeaningInputsLevel : ProofLevel
physicalSelectedReferenceIntegrandMeaningInputsLevel = conditional
