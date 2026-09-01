{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierRound187Exact where

------------------------------------------------------------------------
-- ROUND187 A1 BIDI: PHYSICAL SELECTED BACKGROUND -> EXACT UNIT-QUATERNION
-- PERIODIC REALIZATION BY CONSTRUCTION
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories",
-- Commun. Math. Phys. 102 (1985), 605--636. DOI: 10.1007/BF01229381.
--
-- R185 exposed the last source-side same-object statement as
--
--   realization.bondField = Physical.link(selectedBackground).
--
-- Repository inspection shows the concrete exact periodic SU(2) carrier uses
-- `RationalUnitQuaternion`, whereas the Wilson/variational physical background
-- stores a raw rational quaternion plus an exact unit-norm proof.  Therefore
-- the genuinely canonical construction is to lift each physical link into the
-- sigma-like unit-quaternion carrier and feed it to the already-owned exact
-- periodic bond realization.  No new group-law or covariance receipt is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (PositiveBond)
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond

PhysicalBond4 : Set
PhysicalBond4 = PositiveBond Path4.side4

liftPhysicalLink :
  (background : Physical.RationalSU2Background4) →
  PhysicalBond4 → SU2.RationalUnitQuaternion
liftPhysicalLink background bond
  with Physical.link background bond
     | Physical.unitNorm background bond
... | Q.quat a0 a1 a2 a3 | norm =
  SU2.rationalUnitQuaternion a0 a1 a2 a3 norm

eraseUnitQuaternion : SU2.RationalUnitQuaternion → Q.RationalQuaternion
eraseUnitQuaternion value =
  Q.quat
    (SU2.realPart value)
    (SU2.imagI value)
    (SU2.imagJ value)
    (SU2.imagK value)

eraseLiftPhysicalLink :
  ∀ background bond →
  eraseUnitQuaternion (liftPhysicalLink background bond)
  ≡ Physical.link background bond
eraseLiftPhysicalLink background bond
  with Physical.link background bond
     | Physical.unitNorm background bond
... | Q.quat a0 a1 a2 a3 | norm = refl

physicalBackgroundBondData :
  Physical.RationalSU2Background4 → Carrier.RationalSU2BondData 3
physicalBackgroundBondData background = record
  { Carrier.RationalSU2BondData.links = liftPhysicalLink background
  ; Carrier.RationalSU2BondData.siteGauge = λ _ → Group.identityRationalSU2
  }

physicalBackgroundRealization :
  Physical.RationalSU2Background4 →
  Bond.PeriodicBondGaugeRealization
    3 SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
physicalBackgroundRealization background =
  Carrier.realization (physicalBackgroundBondData background)

physicalBackgroundRealizationBondIsLiftedPhysicalLink :
  ∀ background bond →
  Bond.bondField (physicalBackgroundRealization background) bond
  ≡ liftPhysicalLink background bond
physicalBackgroundRealizationBondIsLiftedPhysicalLink background bond = refl

physicalBackgroundRealizationErasesToPhysicalLink :
  ∀ background bond →
  eraseUnitQuaternion
    (Bond.bondField (physicalBackgroundRealization background) bond)
  ≡ Physical.link background bond
physicalBackgroundRealizationErasesToPhysicalLink = eraseLiftPhysicalLink

cmp98SelectedPhysicalUnitCarrierRound187Level : ProofLevel
cmp98SelectedPhysicalUnitCarrierRound187Level = machineChecked

cmp98SelectedPhysicalPeriodicRealizationRound187Level : ProofLevel
cmp98SelectedPhysicalPeriodicRealizationRound187Level = machineChecked

-- BIDI correction: the remaining source seam is not existence of a periodic
-- realization.  That realization is now constructed from the selected physical
-- background.  What remains for the raw-quaternion Eq.(119) lane is the exact
-- carrier-identification/erasure theorem showing that all group/path operations
-- commute with this unit-quaternion lift.  Search/reuse that representation
-- homomorphism before introducing any new same-object receipt.
literalCMP98RawToUnitCarrierHomomorphismRound187Level : ProofLevel
literalCMP98RawToUnitCarrierHomomorphismRound187Level = conditional
