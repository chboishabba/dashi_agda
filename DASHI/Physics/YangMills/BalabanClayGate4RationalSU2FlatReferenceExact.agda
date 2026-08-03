module DASHI.Physics.YangMills.BalabanClayGate4RationalSU2FlatReferenceExact where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (0ℚ)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (pair; first; second)
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4)

import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as RationalBond
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette

------------------------------------------------------------------------
-- Primary provenance.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press, open-access
-- reissue (2022). DOI: 10.1017/9781009290395.
--
-- The all-identity link field is the canonical flat lattice connection. The
-- negative-oriented link is handled propositionally through inverse(identity)
-- = identity; it is not assumed to be definitionally equal as a proof-carrying
-- rational-unit-quaternion record.
------------------------------------------------------------------------

identityLinks : ∀ n → RationalBond.RationalSU2BondField n
identityLinks n bond = Group.identityRationalSU2

identitySiteGauge : ∀ n → RationalBond.RationalSU2SiteGauge n
identitySiteGauge n site = Group.identityRationalSU2

flatReferenceBondData : ∀ n → RationalBond.RationalSU2BondData n
flatReferenceBondData n = record
  { links = identityLinks n
  ; siteGauge = identitySiteGauge n
  }

flatOrientedLinkIdentity :
  ∀ {n} site direction →
  Bond.orientedLink (RationalBond.realization (flatReferenceBondData n))
    site direction
  ≡ Group.identityRationalSU2
flatOrientedLinkIdentity site (pair axis true) = refl
flatOrientedLinkIdentity site (pair axis false) =
  Path.inverseIdentity Group.rationalSU2ExactLinkGroup

flatPathHolonomyIdentity :
  ∀ {n} site (directions : List SignedAxis4) →
  Bond.pathHolonomy (RationalBond.realization (flatReferenceBondData n))
    site directions
  ≡ Group.identityRationalSU2
flatPathHolonomyIdentity site [] = refl
flatPathHolonomyIdentity {n} site (direction ∷ directions) =
  trans
    (cong₂ (Bond.multiply Group.rationalSU2ExactLinkGroup)
      (flatOrientedLinkIdentity site direction)
      (flatPathHolonomyIdentity
        (Bond.walkStep site direction) directions))
    (Bond.identityLeft Group.rationalSU2ExactLinkGroup
      Group.identityRationalSU2)

flatPlaquetteHolonomyIdentity :
  ∀ {n} (plaquette : Plaquette.PeriodicPlaquette n) →
  RationalBond.rationalSU2PlaquetteHolonomy
    (flatReferenceBondData n) plaquette
  ≡ Group.identityRationalSU2
flatPlaquetteHolonomyIdentity plaquette =
  flatPathHolonomyIdentity (first plaquette)
    (Bond.plaquetteBoundaryDirections (second plaquette))

flatWilsonTraceDeficitZero :
  SU2.wilsonTraceDeficit Group.identityRationalSU2 ≡ 0ℚ
flatWilsonTraceDeficitZero = refl

flatChordalDistanceZero :
  SU2.literalChordalDistanceSq Group.identityRationalSU2 ≡ 0ℚ
flatChordalDistanceZero = refl

flatReferenceDefinitionLevel : ProofLevel
flatReferenceDefinitionLevel = machineChecked

flatOrientedLinkIdentityLevel : ProofLevel
flatOrientedLinkIdentityLevel = machineChecked

flatPathHolonomyIdentityLevel : ProofLevel
flatPathHolonomyIdentityLevel = machineChecked

flatPlaquetteHolonomyIdentityLevel : ProofLevel
flatPlaquetteHolonomyIdentityLevel = machineChecked

flatWilsonCostZeroLevel : ProofLevel
flatWilsonCostZeroLevel = machineChecked

flatReferenceFastFibreMembershipInputsLevel : ProofLevel
flatReferenceFastFibreMembershipInputsLevel = conditional

flatReferenceNonActionFactorPositivityInputsLevel : ProofLevel
flatReferenceNonActionFactorPositivityInputsLevel = conditional
