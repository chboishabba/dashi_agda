module DASHI.Physics.YangMills.BalabanClayGate4T3RestrictedDeterminantAdapterExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4IpsenRehmanDeterminantLossExact as Determinant
import DASHI.Physics.YangMills.BalabanClayGate4T3ConstrainedHessianRestrictionReuseExact as T3Restriction
import DASHI.Physics.YangMills.BalabanClayT3PhysicalUniformFluctuationCoercivityExact as T3

------------------------------------------------------------------------
-- Provenance.
--
-- Ilse C. F. Ipsen and Rizwana Rehman,
-- "Perturbation Bounds for Determinants and Characteristic Polynomials",
-- SIAM Journal on Matrix Analysis and Applications 30 (2008), 762--776.
-- DOI: 10.1137/070704770.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- This module transports the restricted T3 operator-norm estimate into the
-- finite determinant carrier.  It does not postulate that an ambient operator
-- is already a selected finite matrix; that representation remains an explicit
-- proof-bearing field.
------------------------------------------------------------------------

record T3RestrictedDeterminantMeaning
    {Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse : Set}
    (restrictionInputs : T3Restriction.T3ConstrainedRestrictionInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse)
    (scale : Scale) (volume : Volume)
    (regime : PatchRegime) (background : Background)
    (Matrix : Set) : Set₁ where
  field
    normInputs : T3Restriction.T3RestrictedOperatorNormInputs
      restrictionInputs scale volume regime background

    determinantData :
      Determinant.FiniteRelativeDeterminantPerturbation Matrix Bound

    ReferenceMatrixRepresentsRestrictedHessian : Matrix → Set
    PerturbationMatrixRepresentsRestrictedRemainder : Matrix → Set
    PerturbedMatrixRepresentsRestrictedPhysicalHessian : Matrix → Set

    referenceMatrixRepresentsRestrictedHessian :
      ReferenceMatrixRepresentsRestrictedHessian
        (Determinant.referenceMatrix determinantData)

    perturbationMatrixRepresentsRestrictedRemainder :
      PerturbationMatrixRepresentsRestrictedRemainder
        (Determinant.perturbationMatrix determinantData)

    perturbedMatrixRepresentsRestrictedPhysicalHessian :
      PerturbedMatrixRepresentsRestrictedPhysicalHessian
        (Determinant.perturbedMatrix determinantData)

    perturbationNormMeaning :
      Determinant.perturbationNorm determinantData
      ≡ T3Restriction.restrictedRemainderNorm normInputs

    determinantOrderMeaning : ∀ left right →
      Determinant.LessEqual determinantData left right
      ≡ T3.LessEqual (T3Restriction.t3 restrictionInputs) left right

open T3RestrictedDeterminantMeaning public

determinantPerturbationNormBelowT3Epsilon :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse Matrix}
    {restrictionInputs : T3Restriction.T3ConstrainedRestrictionInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse}
    {scale : Scale} {volume : Volume}
    {regime : PatchRegime} {background : Background}
    (meaning : T3RestrictedDeterminantMeaning
      restrictionInputs scale volume regime background Matrix) →
  Determinant.LessEqual (determinantData meaning)
    (Determinant.perturbationNorm (determinantData meaning))
    (T3Restriction.epsilonOperator (normInputs meaning))
determinantPerturbationNormBelowT3Epsilon meaning =
  let
    determinantDataSelected = determinantData meaning
    restrictedNorm =
      T3Restriction.restrictedRemainderNorm (normInputs meaning)
    epsilon = T3Restriction.epsilonOperator (normInputs meaning)
    t3Bound =
      T3Restriction.restrictedT3RemainderBelowOperatorEpsilon
        (normInputs meaning)
    determinantBoundAtRestrictedNorm :
      Determinant.LessEqual determinantDataSelected restrictedNorm epsilon
    determinantBoundAtRestrictedNorm =
      subst
        (λ proposition → proposition)
        (sym (determinantOrderMeaning meaning restrictedNorm epsilon))
        t3Bound
  in
    subst
      (λ lower →
        Determinant.LessEqual determinantDataSelected lower epsilon)
      (sym (perturbationNormMeaning meaning))
      determinantBoundAtRestrictedNorm

t3RestrictedDeterminantRepresentationLevel : ProofLevel
t3RestrictedDeterminantRepresentationLevel = machineChecked

t3PerturbationNormToDeterminantOrderLevel : ProofLevel
t3PerturbationNormToDeterminantOrderLevel = machineChecked

physicalFiniteMatrixRestrictionMeaningInputsLevel : ProofLevel
physicalFiniteMatrixRestrictionMeaningInputsLevel = conditional

physicalDeterminantOrderIdentificationInputsLevel : ProofLevel
physicalDeterminantOrderIdentificationInputsLevel = conditional

physicalReferenceInverseNormIdentificationInputsLevel : ProofLevel
physicalReferenceInverseNormIdentificationInputsLevel = conditional
