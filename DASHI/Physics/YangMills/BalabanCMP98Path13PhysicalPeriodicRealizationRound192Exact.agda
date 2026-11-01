{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact where

------------------------------------------------------------------------
-- ROUND192 REPAIR: SPECIALIZE THE HISTORICAL PERIODIC API TO PHYSICAL SIDE 13
--
-- The historical `PeriodicBondGaugeRealization n` API is predecessor-indexed:
--
--   PeriodicBondField n = BondField (suc n)
--   PeriodicBlock n     = periodicTorus4Definition (suc n).
--
-- Therefore a literal physical side L=13 must use historical index n=12.
-- The earlier version incorrectly passed 13, which would make the historical
-- periodic carrier side 14 while its source background remained side 13.
--
-- This owner now keeps the two coordinates explicit:
--   physical side       = 13,
--   historical index   = 12,
--   suc historicalIndex = physical side.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)

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

path13PeriodicIndex : Nat
path13PeriodicIndex = 12

path13PeriodicIndexSuccessorIsSide13 :
  suc path13PeriodicIndex ≡ Side13.side13
path13PeriodicIndexSuccessorIsSide13 = refl

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

-- `RationalSU2BondData 12` has links on `BondField (suc 12)`, hence exactly
-- `PositiveBond 13`.
path13PhysicalBondData :
  Path13.RationalSU2Background13 →
  Carrier.RationalSU2BondData path13PeriodicIndex
path13PhysicalBondData background = record
  { Carrier.RationalSU2BondData.links = liftPath13Link background
  ; Carrier.RationalSU2BondData.siteGauge = λ _ → Group.identityRationalSU2
  }

path13PhysicalPeriodicRealization :
  Path13.RationalSU2Background13 →
  Bond.PeriodicBondGaugeRealization
    path13PeriodicIndex
    SU2.RationalUnitQuaternion
    Group.rationalSU2ExactLinkGroup
path13PhysicalPeriodicRealization background =
  Carrier.realization (path13PhysicalBondData background)

path13RealizationBondFieldIsLiftedPhysicalLink :
  ∀ background bond →
  Bond.bondField (path13PhysicalPeriodicRealization background) bond
  ≡ liftPath13Link background bond
path13RealizationBondFieldIsLiftedPhysicalLink background bond = refl

path13RealizationErasesToPhysicalLink :
  ∀ background site axis →
  R187.eraseUnitQuaternion
    (Bond.bondField
      (path13PhysicalPeriodicRealization background)
      (pair site axis))
  ≡ Path13.link background axis site
path13RealizationErasesToPhysicalLink background site axis
  with Path13.link background axis site
     | Path13.unitNorm background axis site
... | Q.quat a0 a1 a2 a3 | norm = refl

path13PeriodicPathErasure :
  ∀ background site directions →
  R187.eraseUnitQuaternion
    (Bond.pathHolonomy
      (path13PhysicalPeriodicRealization background) site directions)
  ≡ RawPath.pathProduct
      (Erasure.rawPathFactors
        (path13PhysicalPeriodicRealization background) site directions)
path13PeriodicPathErasure background =
  Erasure.erasedPathHolonomyIsRawPathProduct
    (path13PhysicalPeriodicRealization background)

-- Canonical physical reading of the historical predecessor index.
path13PeriodicRealizationUsesLiteralSide13 :
  suc path13PeriodicIndex ≡ 13
path13PeriodicRealizationUsesLiteralSide13 = refl

cmp98Path13PhysicalPeriodicIndexRepairRound192Level : ProofLevel
cmp98Path13PhysicalPeriodicIndexRepairRound192Level = machineChecked

cmp98Path13PhysicalPeriodicRealizationRound192Level : ProofLevel
cmp98Path13PhysicalPeriodicRealizationRound192Level = machineChecked

cmp98Path13PhysicalCarrierSameObjectRound192Level : ProofLevel
cmp98Path13PhysicalCarrierSameObjectRound192Level = machineChecked

cmp98Path13PeriodicPathErasureRound192Level : ProofLevel
cmp98Path13PeriodicPathErasureRound192Level = machineChecked

literalCMP98Path13Equation119SpecializationRound192Level : ProofLevel
literalCMP98Path13Equation119SpecializationRound192Level = conditional
