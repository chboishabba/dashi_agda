{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13PhysicalUnitCarrierPeriodicRealizationExact where

------------------------------------------------------------------------
-- ROUND195 BIDI SOURCE WELD
--
-- The Path13 physical background already lives on the repository's literal
-- 13^4 site carrier.  `PhysicalBlockL` is definitionally the same object as
-- `periodicTorus4Definition`, so no site reindexing or n = L - 1 translation
-- is needed for periodic positive bonds.  Each raw rational quaternion link
-- carries an exact unit-norm proof; lift that link into the existing exact
-- RationalUnitQuaternion group carrier and reuse the generic periodic bond
-- realization/path algebra.
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Commun. Math. Phys. 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (PositiveBond; pair)
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Path13
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierRound187Exact as R187
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierErasureBridgeExact as Erasure
import DASHI.Physics.YangMills.BalabanCMP109QuaternionPathTransportTelescopeExact as RawPath

Path13PositiveBond : Set
Path13PositiveBond = PositiveBond Side13.side13

liftPath13Link :
  Path13.RationalSU2Background13 →
  Path13PositiveBond → SU2.RationalUnitQuaternion
liftPath13Link background (pair site axis)
  with Path13.link background axis site
     | Path13.unitNorm background axis site
... | Q.quat a0 a1 a2 a3 | norm =
  SU2.rationalUnitQuaternion a0 a1 a2 a3 norm

path13BondData :
  Path13.RationalSU2Background13 →
  Carrier.RationalSU2BondData Side13.side13
path13BondData background = record
  { Carrier.RationalSU2BondData.links = liftPath13Link background
  ; Carrier.RationalSU2BondData.siteGauge = λ _ → Group.identityRationalSU2
  }

path13PeriodicRealization :
  Path13.RationalSU2Background13 →
  Bond.PeriodicBondGaugeRealization
    Side13.side13 SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
path13PeriodicRealization background =
  Carrier.realization (path13BondData background)

path13PeriodicBondIsLiftedPhysicalLink :
  ∀ background bond →
  Bond.bondField (path13PeriodicRealization background) bond
  ≡ liftPath13Link background bond
path13PeriodicBondIsLiftedPhysicalLink background bond = refl

path13PeriodicBondErasesToPhysicalLink :
  ∀ background site axis →
  R187.eraseUnitQuaternion
    (Bond.bondField (path13PeriodicRealization background) (pair site axis))
  ≡ Path13.link background axis site
path13PeriodicBondErasesToPhysicalLink background site axis
  with Path13.link background axis site
     | Path13.unitNorm background axis site
... | Q.quat a0 a1 a2 a3 | norm = refl

-- The exact generic erasure theorem now applies to the literal Path13
-- realization.  This is the same ordered path product used by the raw
-- quaternion principal-chart lane; no parallel path convention is introduced.
path13PeriodicPathErasure :
  ∀ background site directions →
  R187.eraseUnitQuaternion
    (Bond.pathHolonomy (path13PeriodicRealization background) site directions)
  ≡ RawPath.pathProduct
      (Erasure.rawPathFactors
        (path13PeriodicRealization background) site directions)
path13PeriodicPathErasure background =
  Erasure.erasedPathHolonomyIsRawPathProduct
    (path13PeriodicRealization background)

-- Explicitly pin the off-by-one point: the physical Path13 site carrier and
-- the periodic realization both use side13 = 13.  The separate open-fibre
-- `PhysicalPositiveEdge 13` carrier has 12 predecessor edges per fibre, but it
-- is not the site index of `PeriodicBondGaugeRealization`.
path13PeriodicRealizationUsesLiteralSide13 :
  Side13.side13 ≡ 13
path13PeriodicRealizationUsesLiteralSide13 = refl

path13PhysicalUnitLiftLevel : ProofLevel
path13PhysicalUnitLiftLevel = machineChecked

path13PeriodicRealizationLevel : ProofLevel
path13PeriodicRealizationLevel = machineChecked

path13PeriodicBondErasureLevel : ProofLevel
path13PeriodicBondErasureLevel = machineChecked

path13PeriodicPathErasureLevel : ProofLevel
path13PeriodicPathErasureLevel = machineChecked
