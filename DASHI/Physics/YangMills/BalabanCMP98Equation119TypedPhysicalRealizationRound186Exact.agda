{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119TypedPhysicalRealizationRound186Exact where

------------------------------------------------------------------------
-- ROUND186 A1 BIDI: THE SELECTED PHYSICAL BACKGROUND IS ALREADY A TYPED
-- PERIODIC SU(2) BOND REALIZATION
--
-- The physical selected-background owner stores raw rational quaternion
-- coordinates together with a unit-norm theorem for every positive bond.
-- The repository's exact lattice group, however, correctly lives on
-- `RationalUnitQuaternion`, where unit norm is part of the carrier.
--
-- This file packages each physical link into that existing group carrier and
-- constructs `PeriodicBondGaugeRealization` with the identity site gauge.
-- Therefore the bond-field same-object statement is construction, not an
-- equality receipt.  No exact group structure on unrestricted raw quaternions
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Unit
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Raw
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical

------------------------------------------------------------------------
-- Lossless packaging of the physical unit-norm raw link.
------------------------------------------------------------------------

rawUnitQuaternion :
  (value : Raw.RationalQuaternion) →
  Physical.quaternionNormSq value ≡ 1 →
  Unit.RationalUnitQuaternion
rawUnitQuaternion value norm =
  Unit.rationalUnitQuaternion
    (Raw.q0 value)
    (Raw.q1 value)
    (Raw.q2 value)
    (Raw.q3 value)
    norm

forgetUnitQuaternion : Unit.RationalUnitQuaternion → Raw.RationalQuaternion
forgetUnitQuaternion value =
  Raw.quat
    (Unit.realPart value)
    (Unit.imagI value)
    (Unit.imagJ value)
    (Unit.imagK value)

forgetRawUnitQuaternion :
  (value : Raw.RationalQuaternion) →
  (norm : Physical.quaternionNormSq value ≡ 1) →
  forgetUnitQuaternion (rawUnitQuaternion value norm) ≡ value
forgetRawUnitQuaternion (Raw.quat a b c d) norm = refl

physicalUnitLink :
  Physical.RationalSU2Background4 →
  Path4.PhysicalBond4 → Unit.RationalUnitQuaternion
physicalUnitLink background bond =
  rawUnitQuaternion
    (Physical.link background bond)
    (Physical.unitNorm background bond)

physicalUnitLinkForgetsToPhysicalLink :
  (background : Physical.RationalSU2Background4) bond →
  forgetUnitQuaternion (physicalUnitLink background bond)
  ≡ Physical.link background bond
physicalUnitLinkForgetsToPhysicalLink background bond =
  forgetRawUnitQuaternion
    (Physical.link background bond)
    (Physical.unitNorm background bond)

------------------------------------------------------------------------
-- Generic identity-gauge realization.
------------------------------------------------------------------------

inverseIdentity :
  ∀ {Value} (group : Bond.ExactLinkGroup Value) →
  Bond.inverse group (Bond.identity group) ≡ Bond.identity group
inverseIdentity group =
  trans
    (sym (Bond.identityRight group
      (Bond.inverse group (Bond.identity group))))
    (Bond.inverseLeft group (Bond.identity group))

identityGaugeConjugation :
  ∀ {Value} (group : Bond.ExactLinkGroup Value) value →
  Bond.multiply group
    (Bond.multiply group (Bond.identity group) value)
    (Bond.inverse group (Bond.identity group))
  ≡ value
identityGaugeConjugation group value =
  trans
    (cong
      (λ left → Bond.multiply group left
        (Bond.inverse group (Bond.identity group)))
      (Bond.identityLeft group value))
    (trans
      (cong (Bond.multiply group value) (inverseIdentity group))
      (Bond.identityRight group value))

identityGaugeRealization :
  ∀ {n Value}
    (group : Bond.ExactLinkGroup Value) →
  Bond.PeriodicBondField n Value →
  Bond.PeriodicBondGaugeRealization n Value group
identityGaugeRealization {n} group field = record
  { Bond.PeriodicBondGaugeRealization.bondField = field
  ; Bond.PeriodicBondGaugeRealization.gauge = λ _ → Bond.identity group
  ; Bond.PeriodicBondGaugeRealization.orientedLinkGaugeCovariant = covariance
  }
  where
  covariance : ∀ site direction →
    Bond.transformedOrientedLinkBase group field
      (λ _ → Bond.identity group) site direction
    ≡ Bond.multiply group
        (Bond.multiply group (Bond.identity group)
          (Bond.orientedLinkBase group field site direction))
        (Bond.inverse group (Bond.identity group))
  covariance site (pair axis true) = refl
  covariance site (pair axis false) =
    let
      bond = field (pair (Bond.negativeStep site axis) axis)
      transformedPositive :
        Bond.transformedBondBase group field
          (λ _ → Bond.identity group)
          (pair (Bond.negativeStep site axis) axis)
        ≡ bond
      transformedPositive = identityGaugeConjugation group bond
    in
    trans
      (cong (Bond.inverse group) transformedPositive)
      (sym (identityGaugeConjugation group (Bond.inverse group bond)))

------------------------------------------------------------------------
-- Literal side-four selected physical realization.
------------------------------------------------------------------------

physicalSelectedPeriodicRealization :
  Physical.RationalSU2Background4 →
  Bond.PeriodicBondGaugeRealization
    3 Unit.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
physicalSelectedPeriodicRealization background =
  identityGaugeRealization
    Group.rationalSU2ExactLinkGroup
    (physicalUnitLink background)

physicalSelectedBondFieldIsTypedPhysicalLink :
  (background : Physical.RationalSU2Background4) bond →
  Bond.bondField (physicalSelectedPeriodicRealization background) bond
  ≡ physicalUnitLink background bond
physicalSelectedBondFieldIsTypedPhysicalLink background bond = refl

physicalSelectedBondFieldForgetsToRawPhysicalLink :
  (background : Physical.RationalSU2Background4) bond →
  forgetUnitQuaternion
    (Bond.bondField (physicalSelectedPeriodicRealization background) bond)
  ≡ Physical.link background bond
physicalSelectedBondFieldForgetsToRawPhysicalLink background bond =
  physicalUnitLinkForgetsToPhysicalLink background bond

cmp98Equation119TypedPhysicalRealizationRound186Level : ProofLevel
cmp98Equation119TypedPhysicalRealizationRound186Level = machineChecked

cmp98Equation119PhysicalBondFieldDefinitionalRound186Level : ProofLevel
cmp98Equation119PhysicalBondFieldDefinitionalRound186Level = machineChecked

-- The raw-quaternion realization seam is gone at the correct SU(2) carrier.
-- The next BIDI seam is transport of the already-owned selected principal
-- chart/defect semantics across `forgetUnitQuaternion` / `rawUnitQuaternion`.
literalCMP98SelectedChartUnitQuaternionTransportRound186Level : ProofLevel
literalCMP98SelectedChartUnitQuaternionTransportRound186Level = conditional
