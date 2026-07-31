module DASHI.Physics.YangMills.BalabanClayGate4FlatReferencePositiveWitnessExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass

------------------------------------------------------------------------
-- Primary provenance.
--
-- André Weil,
-- "L'intégration dans les groupes topologiques et ses applications",
-- Hermann, Paris (1940). No DOI assigned.
--
-- Gerald B. Folland,
-- "A Course in Abstract Harmonic Analysis", second edition,
-- CRC Press (2016). DOI: 10.1201/b19172.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press, open-access
-- reissue (2022). DOI: 10.1017/9781009290395.
--
-- DASHI already constructs the literal all-identity rational-SU(2) bond field.
-- This module proves the remaining finite implication: membership of a fine
-- representative in the selected fibre, plus strict positivity of the six
-- reference factors, gives the exact positive witness consumed by reference
-- mass normalization.
------------------------------------------------------------------------

record FlatReferenceFactorData
    {Scale Fine SlowField Component Functional Scalar : Set}
    (tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar)
    (positiveAlgebra :
      PositiveMass.PositiveFiniteFoldAlgebra (T.sumData tData)) : Set₁ where
  field
    multiply : Scalar → Scalar → Scalar
    multiplyPositive : ∀ {left right} →
      PositiveMass.Positive positiveAlgebra left →
      PositiveMass.Positive positiveAlgebra right →
      PositiveMass.Positive positiveAlgebra (multiply left right)

    rawSelectedReference : Scale → Component → SlowField → Fine → Scalar

    actionFactor haarFactor determinantFactor bchFactor
      localizationFactor patchFactor :
      Scale → Component → SlowField → Fine → Scalar

    referenceWeightMeaning : ∀ scale component slow fine →
      rawSelectedReference scale component slow fine
      ≡ multiply (actionFactor scale component slow fine)
        (multiply (haarFactor scale component slow fine)
          (multiply (determinantFactor scale component slow fine)
            (multiply (bchFactor scale component slow fine)
              (multiply (localizationFactor scale component slow fine)
                (patchFactor scale component slow fine)))))

    selectedWeightNonnegative : ∀ scale component slow fine →
      PositiveMass.Nonnegative positiveAlgebra
        (rawSelectedReference scale component slow fine)

open FlatReferenceFactorData public

record FlatReferenceInPhysicalFibre
    {Scale Fine SlowField Component Functional Scalar : Set}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    {positiveAlgebra :
      PositiveMass.PositiveFiniteFoldAlgebra (T.sumData tData)}
    (factors : FlatReferenceFactorData tData positiveAlgebra)
    (scale : Scale) (component : Component) (slow : SlowField) : Set₁ where
  field
    flatFine : Fine
    RepresentsCanonicalFlatSU2 : Fine → Set
    flatRepresentsCanonicalSU2 : RepresentsCanonicalFlatSU2 flatFine

    flatInFastFibre :
      PositiveMass._∈_ flatFine (T.fastFibre tData scale component)

    flatCoarseConstraintExact : Set
    flatGaugeRestrictionExact : Set
    flatSupportAndBoundaryRestrictionExact : Set

    flatActionPositive :
      PositiveMass.Positive positiveAlgebra
        (actionFactor factors scale component slow flatFine)
    flatHaarPositive :
      PositiveMass.Positive positiveAlgebra
        (haarFactor factors scale component slow flatFine)
    flatDeterminantPositive :
      PositiveMass.Positive positiveAlgebra
        (determinantFactor factors scale component slow flatFine)
    flatBCHPositive :
      PositiveMass.Positive positiveAlgebra
        (bchFactor factors scale component slow flatFine)
    flatLocalizationPositive :
      PositiveMass.Positive positiveAlgebra
        (localizationFactor factors scale component slow flatFine)
    flatPatchPositive :
      PositiveMass.Positive positiveAlgebra
        (patchFactor factors scale component slow flatFine)

open FlatReferenceInPhysicalFibre public

flatReferenceWeightPositive :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    {positiveAlgebra :
      PositiveMass.PositiveFiniteFoldAlgebra (T.sumData tData)}
    {factors : FlatReferenceFactorData tData positiveAlgebra}
    {scale component slow} →
  (flat : FlatReferenceInPhysicalFibre factors scale component slow) →
  PositiveMass.Positive positiveAlgebra
    (rawSelectedReference factors scale component slow (flatFine flat))
flatReferenceWeightPositive {positiveAlgebra = positiveAlgebra}
  {factors = factors} {scale = scale} {component = component} {slow = slow} flat =
  subst
    (PositiveMass.Positive positiveAlgebra)
    (sym (referenceWeightMeaning factors scale component slow (flatFine flat)))
    (multiplyPositive factors
      (flatActionPositive flat)
      (multiplyPositive factors
        (flatHaarPositive flat)
        (multiplyPositive factors
          (flatDeterminantPositive flat)
          (multiplyPositive factors
            (flatBCHPositive flat)
            (multiplyPositive factors
              (flatLocalizationPositive flat)
              (flatPatchPositive flat))))))

positiveSelectedReferenceFibreFromFlat :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    {positiveAlgebra :
      PositiveMass.PositiveFiniteFoldAlgebra (T.sumData tData)}
    {factors : FlatReferenceFactorData tData positiveAlgebra}
    {scale component slow} →
  FlatReferenceInPhysicalFibre factors scale component slow →
  PositiveMass.PositiveSelectedReferenceFibre positiveAlgebra
    (rawSelectedReference factors scale component slow)
    slow (T.fastFibre tData scale component)
positiveSelectedReferenceFibreFromFlat {factors = factors}
  {scale = scale} {component = component} {slow = slow} flat = record
  { selectedWeightNonnegative =
      selectedWeightNonnegative factors scale component slow
  ; witness = flatFine flat
  ; witnessInFibre = flatInFastFibre flat
  ; witnessWeightPositive = flatReferenceWeightPositive flat
  }

flatFactorProductPositivityLevel : ProofLevel
flatFactorProductPositivityLevel = machineChecked

flatReferencePositiveWitnessAssemblyLevel : ProofLevel
flatReferencePositiveWitnessAssemblyLevel = machineChecked

physicalFlatCoarseConstraintInputsLevel : ProofLevel
physicalFlatCoarseConstraintInputsLevel = conditional

physicalFlatGaugeSupportBoundaryInputsLevel : ProofLevel
physicalFlatGaugeSupportBoundaryInputsLevel = conditional

physicalFlatHaarDeterminantFactorPositivityInputsLevel : ProofLevel
physicalFlatHaarDeterminantFactorPositivityInputsLevel = conditional
