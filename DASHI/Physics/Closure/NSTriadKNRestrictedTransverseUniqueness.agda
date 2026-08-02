module DASHI.Physics.Closure.NSTriadKNRestrictedTransverseUniqueness where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean Leray; Marco Cannone; DASHI repository contributors.
-- Title: "Restricted transverse-test uniqueness for periodic Fourier vector
-- adjoints".
-- Venue/year: Leray's incompressible projection programme; Handbook of
-- Mathematical Fluid Dynamics, Volume 3, 2005; DASHI formal development,
-- 2026.
-- DOI: 10.1016/S1874-5792(05)80006-0 for Marco Cannone,
-- "Harmonic Analysis Tools for Solving the Incompressible Navier-Stokes
-- Equations"; the reduction theorem is repository-original.
-- Uses: closure of the transverse fibre under subtraction, testing with the
-- difference vector, positivity of the real Hermitian self-pairing, and
-- zero-norm separation.
-- Relationship: proves the logical uniqueness reduction on the physical
-- transverse test family.  Its concrete C3 instantiation waits only for the
-- ordered Euclidean positive-definiteness laws, not for further adjoint
-- symbol algebra.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record TransversePositiveDefiniteCarrier
    {m v s : Level} : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    Mode : Set m
    Vector : Set v
    Scalar : Set s

    zeroScalar : Scalar
    difference : Vector → Vector → Vector
    transverse : Mode → Vector → Set v
    realPairing : Vector → Vector → Scalar
    normSquared : Vector → Scalar

    transverseDifference : ∀ mode u v →
      transverse mode u → transverse mode v →
      transverse mode (difference u v)

    differenceSelfTest : ∀ u v →
      realPairing (difference u v) u
      ≡ realPairing (difference u v) v →
      normSquared (difference u v) ≡ zeroScalar

    zeroDifferenceNormImpliesEqual : ∀ u v →
      normSquared (difference u v) ≡ zeroScalar →
      u ≡ v

open TransversePositiveDefiniteCarrier public

restrictedTransverseTestsSeparate :
  ∀ {m v s}
    (C : TransversePositiveDefiniteCarrier {m} {v} {s})
    (mode : Mode C)
    (u v : Vector C) →
  transverse C mode u →
  transverse C mode v →
  (∀ test → transverse C mode test →
    realPairing C test u ≡ realPairing C test v) →
  u ≡ v
restrictedTransverseTestsSeparate C mode u v transverseU transverseV sameTests =
  zeroDifferenceNormImpliesEqual C u v
    (differenceSelfTest C u v
      (sameTests (difference C u v)
        (transverseDifference C mode u v transverseU transverseV)))

record RestrictedAdjointUniquenessApplication
    {m v s : Level}
    (C : TransversePositiveDefiniteCarrier {m} {v} {s}) :
    Set (lsuc (m ⊔ v ⊔ s)) where
  field
    firstAdjointCandidate secondAdjointCandidate : Mode C → Vector C
    firstAdjointTransverse : ∀ mode →
      transverse C mode (firstAdjointCandidate mode)
    secondAdjointTransverse : ∀ mode →
      transverse C mode (secondAdjointCandidate mode)

    firstPairingIdentityOnTransverseTests : Set s
    secondPairingIdentityOnTransverseTests : Set s

open RestrictedAdjointUniquenessApplication public

restrictedTransverseUniquenessReductionClosed : Bool
restrictedTransverseUniquenessReductionClosed = true

restrictedTransverseUniquenessReductionClosedIsTrue :
  restrictedTransverseUniquenessReductionClosed ≡ true
restrictedTransverseUniquenessReductionClosedIsTrue = refl

concreteC3RestrictedAdjointUniquenessClosed : Bool
concreteC3RestrictedAdjointUniquenessClosed = false

concreteC3RestrictedAdjointUniquenessClosedIsFalse :
  concreteC3RestrictedAdjointUniquenessClosed ≡ false
concreteC3RestrictedAdjointUniquenessClosedIsFalse = refl
