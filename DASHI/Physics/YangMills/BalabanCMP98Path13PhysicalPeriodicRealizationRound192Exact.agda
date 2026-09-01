{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact where

------------------------------------------------------------------------
-- ROUND192 A1 BIDI: SPECIALIZE THE GENERIC CMP98 PERIODIC CARRIER TO THE
-- ACTUAL L=13 PHYSICAL BACKGROUND ALREADY OWNED BY THE PATH13 LANE.
--
-- Round191 correctly blocked using the side-four physical realization as an
-- arbitrary-n producer.  But Eq.(119) itself is generic in n, so arbitrary-n
-- physical input is stronger than necessary: one literal physical source scale
-- suffices for a specialized producer.  The Path13 lane already owns exactly
-- such a source object.
--
-- Carrier identities are definitional:
--
--   PhysicalBlockL 13
--     = periodicTorus4Definition 13
--     = PeriodicBlock 12.
--
-- Every Path13 link is a raw rational quaternion with exact unit norm.  We lift
-- it into the canonical RationalUnitQuaternion carrier and reuse the existing
-- RationalSU2BondData -> PeriodicBondGaugeRealization constructor.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (1ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact as Q
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Path13

------------------------------------------------------------------------
-- Raw physical link -> exact SU(2) carrier.
------------------------------------------------------------------------

liftPath13Link :
  (background : Path13.RationalSU2Background13) →
  Bond.PeriodicBondField 12 SU2.RationalUnitQuaternion
liftPath13Link background (pair site axis)
  with Path13.link background axis site
     | Path13.unitNorm background axis site
... | Q.quat a0 a1 a2 a3 | norm =
  SU2.rationalUnitQuaternion a0 a1 a2 a3 norm

erasePath13UnitQuaternion :
  SU2.RationalUnitQuaternion → Q.RationalQuaternion
erasePath13UnitQuaternion value =
  Q.quat
    (SU2.realPart value)
    (SU2.imagI value)
    (SU2.imagJ value)
    (SU2.imagK value)

liftPath13LinkErasesToPhysicalLink :
  ∀ background site axis →
  erasePath13UnitQuaternion
    (liftPath13Link background (pair site axis))
  ≡ Path13.link background axis site
liftPath13LinkErasesToPhysicalLink background site axis
  with Path13.link background axis site
     | Path13.unitNorm background axis site
... | Q.quat a0 a1 a2 a3 | norm = refl

------------------------------------------------------------------------
-- Canonical periodic realization at n=12 (side length 13).
------------------------------------------------------------------------

path13PhysicalBondData :
  Path13.RationalSU2Background13 → Carrier.RationalSU2BondData 12
path13PhysicalBondData background = record
  { Carrier.RationalSU2BondData.links = liftPath13Link background
  ; Carrier.RationalSU2BondData.siteGauge = λ _ → Group.identityRationalSU2
  }

path13PhysicalPeriodicRealization :
  Path13.RationalSU2Background13 →
  Bond.PeriodicBondGaugeRealization
    12 SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
path13PhysicalPeriodicRealization background =
  Carrier.realization (path13PhysicalBondData background)

path13RealizationBondFieldIsLiftedPhysicalLink :
  ∀ background site axis →
  Bond.bondField (path13PhysicalPeriodicRealization background)
    (pair site axis)
  ≡ liftPath13Link background (pair site axis)
path13RealizationBondFieldIsLiftedPhysicalLink background site axis = refl

path13RealizationErasesToPhysicalLink :
  ∀ background site axis →
  erasePath13UnitQuaternion
    (Bond.bondField (path13PhysicalPeriodicRealization background)
      (pair site axis))
  ≡ Path13.link background axis site
path13RealizationErasesToPhysicalLink = liftPath13LinkErasesToPhysicalLink

cmp98Path13PhysicalPeriodicRealizationRound192Level : ProofLevel
cmp98Path13PhysicalPeriodicRealizationRound192Level = machineChecked

cmp98Path13PhysicalCarrierSameObjectRound192Level : ProofLevel
cmp98Path13PhysicalCarrierSameObjectRound192Level = machineChecked

-- BIDI consequence: arbitrary-period physical realization is not required for
-- a source-faithful Eq.(119) instance.  The remaining source task is to feed
-- this literal n=12 realization into the generic Eq.(119) compiler and weld its
-- selected/coarse-background semantics to the existing Path13 source object.
literalCMP98Path13Equation119SpecializationRound192Level : ProofLevel
literalCMP98Path13Equation119SpecializationRound192Level = conditional
