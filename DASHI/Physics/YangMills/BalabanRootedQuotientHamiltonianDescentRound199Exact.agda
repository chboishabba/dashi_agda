{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRootedQuotientHamiltonianDescentRound199Exact where

------------------------------------------------------------------------
-- ROUND199 BIDI: NORMAL-FORM COMPILER FOR FINITE HAMILTONIAN DESCENT.
--
-- R196 does not present the finite physical quotient as an opaque equivalence
-- class.  It gives a canonical rooted representative and an idempotent
-- normalization.  Therefore quotient descent can be least-privilege:
--
--   1. the physical finite Hamiltonian preserves the rooted slice;
--   2. it commutes, pointwise on bonds, with rooted normalization.
--
-- From (1) define H directly on the R196 quotient carrier.  From (2) prove the
-- descended action is exactly the normalized action of H on any raw field.
-- No quotient-recursion axiom, choice, proof irrelevance or function
-- extensionality is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance as Covariance
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanFinitePhysicalGaugeQuotientCarrierRound196Exact as R196

record RootedHamiltonianDescentInputs
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base) : Set₁ where
  field
    hamiltonian :
      Covariance.DirectedGaugeField4 N group →
      Covariance.DirectedGaugeField4 N group

    hamiltonianPreservesRootedSlice :
      ∀ quotient →
      Rooted.RadialGaugeField group paths
        (hamiltonian (R196.representativeField quotient))

    hamiltonianCommutesWithRootedNormalization :
      ∀ field bond →
      R196.representativeField
        (R196.normalizeToFiniteRootedGaugeQuotient group base paths
          (hamiltonian field)) bond
      ≡ hamiltonian
          (R196.representativeField
            (R196.normalizeToFiniteRootedGaugeQuotient group base paths field))
          bond

open RootedHamiltonianDescentInputs public

rootedQuotientHamiltonian :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  RootedHamiltonianDescentInputs group base paths →
  R196.FiniteRootedGaugeQuotientCarrier group base paths →
  R196.FiniteRootedGaugeQuotientCarrier group base paths
rootedQuotientHamiltonian inputs quotient = record
  { R196.FiniteRootedGaugeQuotientCarrier.representativeField =
      hamiltonian inputs (R196.representativeField quotient)
  ; R196.FiniteRootedGaugeQuotientCarrier.representativeIsRooted =
      hamiltonianPreservesRootedSlice inputs quotient
  }

rootedQuotientHamiltonianRepresentativeExact :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (inputs : RootedHamiltonianDescentInputs group base paths)
    quotient bond →
  R196.representativeField
    (rootedQuotientHamiltonian inputs quotient) bond
  ≡ hamiltonian inputs (R196.representativeField quotient) bond
rootedQuotientHamiltonianRepresentativeExact inputs quotient bond = refl

-- The quotient action on the normalized raw field agrees pointwise with
-- normalizing the raw Hamiltonian output.  This is the same-object handoff the
-- terminal carrier needs.
rootedQuotientHamiltonianCommutesWithNormalization :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (inputs : RootedHamiltonianDescentInputs group base paths)
    field bond →
  R196.representativeField
    (R196.normalizeToFiniteRootedGaugeQuotient group base paths
      (hamiltonian inputs field)) bond
  ≡ R196.representativeField
      (rootedQuotientHamiltonian inputs
        (R196.normalizeToFiniteRootedGaugeQuotient group base paths field)) bond
rootedQuotientHamiltonianCommutesWithNormalization inputs field bond =
  hamiltonianCommutesWithRootedNormalization inputs field bond

rootedQuotientHamiltonianDescentRound199Level : ProofLevel
rootedQuotientHamiltonianDescentRound199Level = machineChecked

rootedQuotientHamiltonianNormalizationHandoffRound199Level : ProofLevel
rootedQuotientHamiltonianNormalizationHandoffRound199Level = machineChecked

-- Physical leaves after the generic quotient machinery is removed.
literalFiniteYMHamiltonianPreservesRootedSliceRound199Level : ProofLevel
literalFiniteYMHamiltonianPreservesRootedSliceRound199Level = conditional

literalFiniteYMHamiltonianCommutesWithRootedNormalizationRound199Level : ProofLevel
literalFiniteYMHamiltonianCommutesWithRootedNormalizationRound199Level = conditional
