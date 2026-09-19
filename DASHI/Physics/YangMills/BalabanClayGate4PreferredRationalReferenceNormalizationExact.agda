module DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact where

------------------------------------------------------------------------
-- PREFERRED GATE4 REFERENCE NORMALIZATION ON LITERAL RATIONAL ALGEBRAS
--
-- This compiler removes scalar-ABI freedom from the preferred finite reference
-- route.  It fixes:
--
--   finite sum     = canonical rational constrained sum
--   zero/add       = 0 and +
--   reference one  = 1
--   multiplication = *
--   nonnegative    = 0 <= q
--   positive       = 0 < q
--   reciprocal     = canonical constructive rational reciprocal
--
-- The remaining inputs are physical: the six-factor reference data, the
-- canonical flat/reference configuration and the selected reference-integrand
-- meaning.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalReferenceAlgebraExact as Algebra
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalReferenceNormalizationExact as Canonical
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalReferenceFactorAssemblyExact as Factor
import DASHI.Physics.YangMills.BalabanClayGate4FlatReferencePositiveWitnessExact as Flat
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceToFiniteRGProbabilityExact as Probability
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

record PreferredRationalReferenceNormalizationInputs
    {Scale Fine SlowField Component Functional : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional} : Set₁ where
  field
    factors :
      Flat.FlatReferenceFactorData
        (PhysicalT.canonicalPhysicalTData construction)
        (Algebra.canonicalPositiveFoldAlgebra
          (PhysicalT.sumCarrier construction))

    canonicalReferenceInputs : ∀ scale component slow →
      Factor.CanonicalReferenceFactorInputs
        factors scale component slow

    suppression : Scale → ℚ
    referenceIntegrand : Scale → Component → SlowField → Fine → ℚ

    selectedReferenceIntegrandMeaning :
      ∀ scale component slow fine →
      Integral.selectedWith
        (T.sumData
          (PhysicalT.canonicalPhysicalTData construction))
        (referenceIntegrand scale component slow)
        slow fine
      ≡
      Reference.scaledSelector
        (Algebra.canonicalReferenceAlgebra
          (PhysicalT.sumCarrier construction))
        (suppression scale)
        (Reference.normalizedReferenceSelector
          (PositiveMass.reciprocalReferenceMassFromPositiveWitness
            (Reciprocal.rationalPositiveMassReciprocalAlgebra
              (Algebra.canonicalRationalPositiveMassInterpretation
                (PhysicalT.sumCarrier construction)))
            (Flat.positiveSelectedReferenceFibreFromFlat
              (Factor.asFlatReferenceInPhysicalFibre
                (canonicalReferenceInputs scale component slow)))))
        fine

open PreferredRationalReferenceNormalizationInputs public

compilePreferredRationalReferenceNormalization :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional} →
  PreferredRationalReferenceNormalizationInputs
    {construction = construction} →
  Canonical.CanonicalRationalReferenceNormalizationData
    Scale Fine SlowField Component Functional
    (PhysicalT.canonicalPhysicalTData construction)
compilePreferredRationalReferenceNormalization
  {construction = construction} inputs = record
  { referenceAlgebra =
      Algebra.canonicalReferenceAlgebra
        (PhysicalT.sumCarrier construction)
  ; positiveAlgebra =
      Algebra.canonicalPositiveFoldAlgebra
        (PhysicalT.sumCarrier construction)
  ; factors = factors inputs
  ; rationalInterpretation =
      Algebra.canonicalRationalPositiveMassInterpretation
        (PhysicalT.sumCarrier construction)
  ; canonicalReferenceInputs =
      canonicalReferenceInputs inputs
  ; suppression = suppression inputs
  ; referenceIntegrand = referenceIntegrand inputs
  ; selectedReferenceIntegrandMeaning =
      selectedReferenceIntegrandMeaning inputs
  }

preferredRationalReferenceConeMeaning :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (inputs :
      PreferredRationalReferenceNormalizationInputs
        {construction = construction}) →
  PhysicalT.RationalReferenceConeMeaning
    (compilePreferredRationalReferenceNormalization inputs)
preferredRationalReferenceConeMeaning inputs = record
  { nonnegativeMeansRationalNonnegative =
      λ nonnegative → nonnegative
  }

preferredRationalReferenceFoldSemantics :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (inputs :
      PreferredRationalReferenceNormalizationInputs
        {construction = construction}) →
  Probability.RationalReferenceFoldSemantics
    (compilePreferredRationalReferenceNormalization inputs)
preferredRationalReferenceFoldSemantics inputs =
  PhysicalT.canonicalRationalReferenceFoldSemantics
    (preferredRationalReferenceConeMeaning inputs)

preferredRationalReferenceNormalizationCompilerLevel : ProofLevel
preferredRationalReferenceNormalizationCompilerLevel = machineChecked

preferredRationalReferenceConeCompilerLevel : ProofLevel
preferredRationalReferenceConeCompilerLevel = machineChecked

preferredRationalReferenceFoldSemanticsCompilerLevel : ProofLevel
preferredRationalReferenceFoldSemanticsCompilerLevel = machineChecked

-- The surviving inputs are physical/reference meaning, not scalar algebra.
preferredReferenceFactorInputsLevel : ProofLevel
preferredReferenceFactorInputsLevel = conditional

preferredSelectedReferenceIntegrandMeaningLevel : ProofLevel
preferredSelectedReferenceIntegrandMeaningLevel = conditional
