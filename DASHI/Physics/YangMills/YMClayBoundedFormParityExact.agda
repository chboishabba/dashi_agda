{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayBoundedFormParityExact where

------------------------------------------------------------------------
-- AGDA PARITY FOR LEAN RequestProject.YangMills.Clay.FormHamiltonian
--
-- The Lean tranche constructs the bounded Hamiltonian by Riesz and derives
-- self-adjointness, vacuum annihilation and the finite vacuum-gap datum from a
-- bounded Hermitian energy form.  Agda already owns the canonical closed-form
-- -> associated self-adjoint Hamiltonian route in
-- YMKatoClosedFormHamiltonianExact.  This module does not create a competing
-- operator theory: it gives the bounded-form consumer shape and factors the
-- operator construction through the canonical Kato owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMKatoClosedFormHamiltonianExact as Kato

record BoundedHermitianEnergyForm
    (Hilbert Scalar : Set) : Set₁ where
  field
    closedSemiboundedForm : Kato.ClosedSemiboundedFormData Hilbert Scalar

    BoundedForm : Set
    boundedForm : BoundedForm

    HermitianForm : Set
    hermitianForm : HermitianForm

open BoundedHermitianEnergyForm public

-- The Lean Riesz construction is represented on the Agda side by a thin
-- factorisation witness into the already-canonical Kato representation owner.
-- This is theorem authority, not a physical Yang--Mills inhabitant.
record BoundedFormRepresentationBridge
    (Hilbert Scalar : Set) : Set₁ where
  field
    authority : Kato.KatoFirstRepresentationAuthority Hilbert Scalar

open BoundedFormRepresentationBridge public

boundedAssociatedHamiltonian :
  ∀ {Hilbert Scalar}
    (bridge : BoundedFormRepresentationBridge Hilbert Scalar)
    (energy : BoundedHermitianEnergyForm Hilbert Scalar) →
  Kato.AssociatedSelfAdjointOperator (closedSemiboundedForm energy)
boundedAssociatedHamiltonian bridge energy =
  Kato.associatedHamiltonian (authority bridge) (closedSemiboundedForm energy)

record BoundedFormGapPackage
    (Hilbert Scalar : Set) : Set₁ where
  field
    energyForm : BoundedHermitianEnergyForm Hilbert Scalar
    representation : BoundedFormRepresentationBridge Hilbert Scalar

    vacuum : Hilbert
    NormalizedVacuum : Set
    normalizedVacuum : NormalizedVacuum

    VacuumNullForm : Set
    vacuumNullForm : VacuumNullForm

    VacuumOrthogonal : Hilbert → Set

    GapParameter : Set
    gapParameter : GapParameter

    CoerciveOnVacuumComplement : Set
    coerciveOnVacuumComplement : CoerciveOnVacuumComplement

  hamiltonian :
    Kato.AssociatedSelfAdjointOperator (closedSemiboundedForm energyForm)
  hamiltonian = boundedAssociatedHamiltonian representation energyForm

open BoundedFormGapPackage public

-- The package exposes exactly the finite information consumed downstream.
-- Self-adjointness is not a separate input: it is projected from the associated
-- Hamiltonian produced by the canonical representation compiler.
boundedFormSelfAdjoint :
  ∀ {Hilbert Scalar}
    (package : BoundedFormGapPackage Hilbert Scalar) → Set
boundedFormSelfAdjoint package =
  Kato.SelfAdjointOnDomain (hamiltonian package)

boundedFormSelfAdjointProof :
  ∀ {Hilbert Scalar}
    (package : BoundedFormGapPackage Hilbert Scalar) →
  boundedFormSelfAdjoint package
boundedFormSelfAdjointProof package =
  Kato.selfAdjointOnDomain (hamiltonian package)

boundedFormHamiltonianCompilerLevel : ProofLevel
boundedFormHamiltonianCompilerLevel = machineChecked

boundedFormRepresentationAuthorityLevel : ProofLevel
boundedFormRepresentationAuthorityLevel =
  Kato.katoFirstRepresentationTheoremAuthorityLevel

literalPhysicalBoundedEnergyFormLevel : ProofLevel
literalPhysicalBoundedEnergyFormLevel = conditional

literalVacuumNullFormLevel : ProofLevel
literalVacuumNullFormLevel = conditional

literalVacuumComplementCoercivityLevel : ProofLevel
literalVacuumComplementCoercivityLevel = conditional

boundedFormParityImplemented : Bool
boundedFormParityImplemented = true

boundedFormParityImplementedIsTrue : boundedFormParityImplemented ≡ true
boundedFormParityImplementedIsTrue = refl

-- No physical object is promoted by this parity compiler.
physicalYangMillsFormConstructedHere : Bool
physicalYangMillsFormConstructedHere = false

physicalYangMillsFormConstructedHereIsFalse :
  physicalYangMillsFormConstructedHere ≡ false
physicalYangMillsFormConstructedHereIsFalse = refl
