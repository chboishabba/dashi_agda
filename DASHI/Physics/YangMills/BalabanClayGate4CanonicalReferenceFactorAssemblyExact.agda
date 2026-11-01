module DASHI.Physics.YangMills.BalabanClayGate4CanonicalReferenceFactorAssemblyExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass
import DASHI.Physics.YangMills.BalabanClayGate4FlatReferencePositiveWitnessExact as Flat

------------------------------------------------------------------------
-- Provenance.
--
-- This is a repository assembly theorem over the physical factor owners. The
-- action, Haar and determinant lanes retain their own primary references. BCH,
-- localization and patch factors are required to identify their canonical
-- reference values exactly with the multiplicative unit.
------------------------------------------------------------------------

record CanonicalReferenceFactorInputs
    {Scale Fine SlowField Component Functional Scalar : Set}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    {positiveAlgebra :
      PositiveMass.PositiveFiniteFoldAlgebra (T.sumData tData)}
    (factors : Flat.FlatReferenceFactorData tData positiveAlgebra)
    (scale : Scale) (component : Component) (slow : SlowField) : Set₁ where
  field
    referenceFine : Fine
    RepresentsCanonicalBackground : Fine → Set
    representsCanonicalBackground : RepresentsCanonicalBackground referenceFine

    referenceInFastFibre :
      PositiveMass._∈_ referenceFine (T.fastFibre tData scale component)

    coarseConstraintExact : Set
    gaugeRestrictionExact : Set
    supportAndBoundaryRestrictionExact : Set

    multiplicativeOne : Scalar
    multiplicativeOnePositive :
      PositiveMass.Positive positiveAlgebra multiplicativeOne

    actionPositive :
      PositiveMass.Positive positiveAlgebra
        (Flat.actionFactor factors scale component slow referenceFine)
    haarPositive :
      PositiveMass.Positive positiveAlgebra
        (Flat.haarFactor factors scale component slow referenceFine)
    determinantPositive :
      PositiveMass.Positive positiveAlgebra
        (Flat.determinantFactor factors scale component slow referenceFine)

    bchAtReferenceOne :
      Flat.bchFactor factors scale component slow referenceFine
      ≡ multiplicativeOne
    localizationAtReferenceOne :
      Flat.localizationFactor factors scale component slow referenceFine
      ≡ multiplicativeOne
    patchAtReferenceOne :
      Flat.patchFactor factors scale component slow referenceFine
      ≡ multiplicativeOne

open CanonicalReferenceFactorInputs public

bchReferencePositive :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    {positiveAlgebra :
      PositiveMass.PositiveFiniteFoldAlgebra (T.sumData tData)}
    {factors : Flat.FlatReferenceFactorData tData positiveAlgebra}
    {scale component slow} →
  (inputs : CanonicalReferenceFactorInputs factors scale component slow) →
  PositiveMass.Positive positiveAlgebra
    (Flat.bchFactor factors scale component slow (referenceFine inputs))
bchReferencePositive {positiveAlgebra = positiveAlgebra} inputs =
  subst (PositiveMass.Positive positiveAlgebra)
    (sym (bchAtReferenceOne inputs))
    (multiplicativeOnePositive inputs)

localizationReferencePositive :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    {positiveAlgebra :
      PositiveMass.PositiveFiniteFoldAlgebra (T.sumData tData)}
    {factors : Flat.FlatReferenceFactorData tData positiveAlgebra}
    {scale component slow} →
  (inputs : CanonicalReferenceFactorInputs factors scale component slow) →
  PositiveMass.Positive positiveAlgebra
    (Flat.localizationFactor factors scale component slow (referenceFine inputs))
localizationReferencePositive {positiveAlgebra = positiveAlgebra} inputs =
  subst (PositiveMass.Positive positiveAlgebra)
    (sym (localizationAtReferenceOne inputs))
    (multiplicativeOnePositive inputs)

patchReferencePositive :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    {positiveAlgebra :
      PositiveMass.PositiveFiniteFoldAlgebra (T.sumData tData)}
    {factors : Flat.FlatReferenceFactorData tData positiveAlgebra}
    {scale component slow} →
  (inputs : CanonicalReferenceFactorInputs factors scale component slow) →
  PositiveMass.Positive positiveAlgebra
    (Flat.patchFactor factors scale component slow (referenceFine inputs))
patchReferencePositive {positiveAlgebra = positiveAlgebra} inputs =
  subst (PositiveMass.Positive positiveAlgebra)
    (sym (patchAtReferenceOne inputs))
    (multiplicativeOnePositive inputs)

asFlatReferenceInPhysicalFibre :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    {positiveAlgebra :
      PositiveMass.PositiveFiniteFoldAlgebra (T.sumData tData)}
    {factors : Flat.FlatReferenceFactorData tData positiveAlgebra}
    {scale component slow} →
  CanonicalReferenceFactorInputs factors scale component slow →
  Flat.FlatReferenceInPhysicalFibre factors scale component slow
asFlatReferenceInPhysicalFibre inputs = record
  { flatFine = referenceFine inputs
  ; RepresentsCanonicalFlatSU2 = RepresentsCanonicalBackground inputs
  ; flatRepresentsCanonicalSU2 = representsCanonicalBackground inputs
  ; flatInFastFibre = referenceInFastFibre inputs
  ; flatCoarseConstraintExact = coarseConstraintExact inputs
  ; flatGaugeRestrictionExact = gaugeRestrictionExact inputs
  ; flatSupportAndBoundaryRestrictionExact = supportAndBoundaryRestrictionExact inputs
  ; flatActionPositive = actionPositive inputs
  ; flatHaarPositive = haarPositive inputs
  ; flatDeterminantPositive = determinantPositive inputs
  ; flatBCHPositive = bchReferencePositive inputs
  ; flatLocalizationPositive = localizationReferencePositive inputs
  ; flatPatchPositive = patchReferencePositive inputs
  }

canonicalReferenceUnitFactorPositivityLevel : ProofLevel
canonicalReferenceUnitFactorPositivityLevel = machineChecked

canonicalReferenceFactorAssemblyLevel : ProofLevel
canonicalReferenceFactorAssemblyLevel = machineChecked

physicalCanonicalReferenceActionInputsLevel : ProofLevel
physicalCanonicalReferenceActionInputsLevel = conditional

physicalCanonicalReferenceHaarInputsLevel : ProofLevel
physicalCanonicalReferenceHaarInputsLevel = conditional

physicalCanonicalReferenceDeterminantInputsLevel : ProofLevel
physicalCanonicalReferenceDeterminantInputsLevel = conditional

physicalCanonicalReferenceUnitFactorMeaningInputsLevel : ProofLevel
physicalCanonicalReferenceUnitFactorMeaningInputsLevel = conditional
