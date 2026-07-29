module DASHI.Physics.YangMills.BalabanClayGate4RationalSU2IdentityConfigurationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (0ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
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
-- proofs below are literal recursion over the repository's path holonomy.
------------------------------------------------------------------------

identityLinks : ∀ n → RationalBond.RationalSU2BondField n
identityLinks n bond = Group.identityRationalSU2

identitySiteGauge : ∀ n → RationalBond.RationalSU2SiteGauge n
identitySiteGauge n site = Group.identityRationalSU2

identityBondData : ∀ n → RationalBond.RationalSU2BondData n
identityBondData n = record
  { RationalBond.RationalSU2BondData.links = identityLinks n
  ; RationalBond.RationalSU2BondData.siteGauge = identitySiteGauge n
  }

identityPathHolonomy :
  ∀ {n} site (directions : List
    DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact.SignedAxis4) →
  Bond.pathHolonomy (RationalBond.realization (identityBondData n))
    site directions
  ≡ Group.identityRationalSU2
identityPathHolonomy site [] = refl
identityPathHolonomy {n} site (direction ∷ directions) =
  trans
    (cong
      (Bond.multiply Group.rationalSU2ExactLinkGroup
        Group.identityRationalSU2)
      (identityPathHolonomy
        (Bond.walkStep site direction) directions))
    (Bond.identityLeft Group.rationalSU2ExactLinkGroup
      Group.identityRationalSU2)

identityPlaquetteHolonomy :
  ∀ {n} (plaquette : Plaquette.PeriodicPlaquette n) →
  RationalBond.rationalSU2PlaquetteHolonomy
    (identityBondData n) plaquette
  ≡ Group.identityRationalSU2
identityPlaquetteHolonomy plaquette =
  identityPathHolonomy _ _

identityWilsonTraceDeficitZero :
  SU2.wilsonTraceDeficit Group.identityRationalSU2 ≡ 0ℚ
identityWilsonTraceDeficitZero = refl

identityChordalDistanceZero :
  SU2.literalChordalDistanceSq Group.identityRationalSU2 ≡ 0ℚ
identityChordalDistanceZero = refl

identityConfigurationDefinitionLevel : ProofLevel
identityConfigurationDefinitionLevel = machineChecked

identityPathHolonomyLevel : ProofLevel
identityPathHolonomyLevel = machineChecked

identityPlaquetteHolonomyLevel : ProofLevel
identityPlaquetteHolonomyLevel = machineChecked

identityWilsonCostZeroLevel : ProofLevel
identityWilsonCostZeroLevel = machineChecked

identityConfigurationFastFibreMembershipInputsLevel : ProofLevel
identityConfigurationFastFibreMembershipInputsLevel = conditional

identityConfigurationNonActionFactorPositivityInputsLevel : ProofLevel
identityConfigurationNonActionFactorPositivityInputsLevel = conditional
