{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMKatoClosedFormHamiltonianExact where

------------------------------------------------------------------------
-- CLOSED SEMIBOUNDED FORM -> ASSOCIATED SELF-ADJOINT HAMILTONIAN
--
-- Source authority:
-- Tosio Kato, Perturbation Theory for Linear Operators,
-- DOI 10.1007/978-3-642-66282-9.
--
-- This is a theorem-interface/compiler, not a proof of Kato's representation
-- theorem and not a physical Yang--Mills instantiation.  It makes the M7 cut
-- precise: once the selected gauge-invariant carrier carries the physical
-- densely-defined closed semibounded form, the representation theorem returns
-- an operator domain and a self-adjoint associated operator.  A chosen common
-- invariant operator core and the action-variation/same-object weld remain
-- separate physical obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record ClosedSemiboundedFormData
    (Hilbert Scalar : Set) : Set₁ where
  field
    Pairing : Hilbert → Hilbert → Scalar
    FormDomain : Hilbert → Set
    form : Hilbert → Hilbert → Scalar

    DenseFormDomain : Set
    formDomainDense : DenseFormDomain

    ClosedForm : Set
    formClosed : ClosedForm

    SemiboundedForm : Set
    formSemibounded : SemiboundedForm

open ClosedSemiboundedFormData public

record AssociatedSelfAdjointOperator
    {Hilbert Scalar : Set}
    (formData : ClosedSemiboundedFormData Hilbert Scalar) : Set₁ where
  field
    OperatorDomain : Hilbert → Set
    operator : Hilbert → Hilbert

    SelfAdjointOnDomain : Set
    selfAdjointOnDomain : SelfAdjointOnDomain

    operatorDomainInsideFormDomain : ∀ vector →
      OperatorDomain vector → FormDomain formData vector

    associatedWithForm : ∀ vector test →
      OperatorDomain vector →
      FormDomain formData test →
      Pairing formData (operator vector) test ≡ form formData vector test

open AssociatedSelfAdjointOperator public

record KatoFirstRepresentationAuthority
    (Hilbert Scalar : Set) : Set₁ where
  field
    associate :
      (formData : ClosedSemiboundedFormData Hilbert Scalar) →
      AssociatedSelfAdjointOperator formData

open KatoFirstRepresentationAuthority public

associatedHamiltonian :
  ∀ {Hilbert Scalar}
    (authority : KatoFirstRepresentationAuthority Hilbert Scalar)
    (formData : ClosedSemiboundedFormData Hilbert Scalar) →
  AssociatedSelfAdjointOperator formData
associatedHamiltonian = associate

record CommonInvariantOperatorCore
    {Hilbert Scalar : Set}
    {formData : ClosedSemiboundedFormData Hilbert Scalar}
    (hamiltonian : AssociatedSelfAdjointOperator formData) : Set₁ where
  field
    Core : Hilbert → Set

    DenseCore : Set
    coreDense : DenseCore

    coreInsideOperatorDomain : ∀ vector →
      Core vector → OperatorDomain hamiltonian vector

    coreInvariant : ∀ vector →
      Core vector → Core (operator hamiltonian vector)

open CommonInvariantOperatorCore public

record PhysicalYMClosedFormInput
    (Hilbert Scalar : Set) : Set₁ where
  field
    selectedGaugeInvariantCarrier : Set
    selectedCarrierIsHilbert : selectedGaugeInvariantCarrier ≡ Hilbert

    physicalForm : ClosedSemiboundedFormData Hilbert Scalar

open PhysicalYMClosedFormInput public

record KatoM7OperatorPackage
    (Hilbert Scalar : Set) : Set₁ where
  field
    physical : PhysicalYMClosedFormInput Hilbert Scalar
    authority : KatoFirstRepresentationAuthority Hilbert Scalar

  hamiltonian : AssociatedSelfAdjointOperator (physicalForm physical)
  hamiltonian = associate authority (physicalForm physical)

open KatoM7OperatorPackage public

katoDomainAndSelfAdjointCompiler :
  ∀ {Hilbert Scalar} →
  KatoM7OperatorPackage Hilbert Scalar →
  AssociatedSelfAdjointOperator
    (physicalForm (KatoM7OperatorPackage.physical _))
katoDomainAndSelfAdjointCompiler package =
  KatoM7OperatorPackage.hamiltonian package

katoClosedFormHamiltonianCompilerLevel : ProofLevel
katoClosedFormHamiltonianCompilerLevel = machineChecked

katoFirstRepresentationTheoremAuthorityLevel : ProofLevel
katoFirstRepresentationTheoremAuthorityLevel = standardImported

literalPhysicalYMClosedSemiboundedFormLevel : ProofLevel
literalPhysicalYMClosedSemiboundedFormLevel = conditional

literalPhysicalYMCommonInvariantOperatorCoreLevel : ProofLevel
literalPhysicalYMCommonInvariantOperatorCoreLevel = conditional

-- Important non-implications preserved by the API:
--
--   associated self-adjoint operator
--     does not construct the selected common invariant core;
--
--   associated self-adjoint operator
--     does not identify the form/operator with the physical action variation;
--
--   finite/physical M7 closure
--     does not imply OS reconstruction, continuum recovery, or Clay promotion.
