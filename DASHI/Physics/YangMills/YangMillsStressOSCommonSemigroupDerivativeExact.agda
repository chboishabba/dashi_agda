{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsStressOSCommonSemigroupDerivativeExact where

------------------------------------------------------------------------
-- L7 CORRECT EUCLIDEAN SEMIGROUP CUT.
--
-- OS Euclidean time is T(t) = exp(-t H_OS), t >= 0.  Its derivative on
-- D(H_OS) is -H_OS, NOT a unitary group derivative i H_OS.
--
-- If a renormalized stress charge Q has a Ward identity showing that
-- the SAME right strong derivative of T(t) is -Q on a common dense core,
-- then Q=H_OS there by uniqueness of the norm limit.  If their closures
-- are both the same self-adjoint operator on that core, equality follows
-- on the full operator domain by the standard core-closure theorem.
--
-- This module proves the exact on-core identification (no postulates);
-- Hilbert norm-limit uniqueness, common core, essential self-adjointness,
-- actual stress Ward source and graph closure are physical/standard
-- responsibilities external to this module. This is not an OS gap proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

record CommonOSSemigroupDerivative
    (Hilbert Time : Set) : Set₁ where
  field
    Core : Hilbert → Set
    euclideanTimeTranslation : Time → Hilbert → Hilbert
    osHamiltonian : Hilbert → Hilbert
    renormalizedStressCharge : Hilbert → Hilbert
    minus : Hilbert → Hilbert
    minusInjective : ∀ {u v} → minus u ≡ minus v → u ≡ v

    -- This is the UNIQUE right norm-derivative of the SAME semigroup
    -- on Core, not an unrelated field or a freely varying Hamiltonian.
    rightStrongDerivative : Hilbert → Hilbert

    osInfinitesimalSemigroupLaw :
      ∀ (psi : Hilbert) → Core psi →
      rightStrongDerivative psi ≡ minus (osHamiltonian psi)

    stressWardRightStrongDerivative :
      ∀ (psi : Hilbert) → Core psi →
      rightStrongDerivative psi ≡ minus (renormalizedStressCharge psi)

open CommonOSSemigroupDerivative public

stressChargeEqualsOSHamiltonianOnCore :
  ∀ {Hilbert Time}
    (dataSet : CommonOSSemigroupDerivative Hilbert Time)
    (psi : Hilbert) →
    Core dataSet psi →
    renormalizedStressCharge dataSet psi ≡ osHamiltonian dataSet psi
stressChargeEqualsOSHamiltonianOnCore dataSet psi belongs =
  minusInjective dataSet
    (trans
      (sym (stressWardRightStrongDerivative dataSet psi belongs))
      (osInfinitesimalSemigroupLaw dataSet psi belongs))

-- Precise next logical step: the common core must be a graph core for
-- H_OS, and Q must be essentially self-adjoint on that core.  At that
-- point, standard uniqueness of the closure identifies Q with H_OS.
-- It is deliberately NOT asserted as a proof term without the Hilbert
-- topology, dense graph-core and limit semantics.

record ClosedStressOSOperatorIdentification
    (Hilbert Time : Set) : Set₁ where
  field
    coreData : CommonOSSemigroupDerivative Hilbert Time
    Operator : Set
    osClosedOperator : Operator
    stressClosedOperator : Operator

    -- Proper functional-analysis theorem instance; the source must
    -- supply graph-core, self-adjointness, and limit topology here.
    sameClosedOperatorFromCommonCore :
      (∀ psi → Core coreData psi →
        renormalizedStressCharge coreData psi
          ≡ osHamiltonian coreData psi) →
      stressClosedOperator ≡ osClosedOperator

open ClosedStressOSOperatorIdentification public

stressOSClosedOperatorsEqual :
  ∀ {Hilbert Time}
    (dataSet : ClosedStressOSOperatorIdentification Hilbert Time) →
    stressClosedOperator dataSet ≡ osClosedOperator dataSet
stressOSClosedOperatorsEqual dataSet =
  sameClosedOperatorFromCommonCore dataSet
    (stressChargeEqualsOSHamiltonianOnCore (coreData dataSet))
