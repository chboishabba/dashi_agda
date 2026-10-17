module DASHI.Physics.QuantumVacuum.CasimirQuaternionSU2GroupLawBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.SU2CompactLieAlgebraInstance as GenericSU2
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Gauge
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as SU2

------------------------------------------------------------------------
-- QUATERNION SU(2): NEW COMPACT-LIE CORE <-> LEGACY GAUGE GROUP LAW
--
-- The newer compact-Lie lane and the older Balaban gauge-transport lane use
-- different record types, but their concrete SU(2) instances use literally the
-- same carrier and the same identity/multiplication/inverse functions.  This
-- file owns that adapter once so selected-QFT consumers do not pay another
-- group-law identification after identifying their structural group with the
-- live quaternionic SU(2) Core.Group.
------------------------------------------------------------------------

genericSU2Carrier : Set
genericSU2Carrier = SU2.SU2Quaternion

genericSU2Identity : genericSU2Carrier
genericSU2Identity = Core.identity GenericSU2.su2GenericGroup

genericSU2Multiply : genericSU2Carrier → genericSU2Carrier → genericSU2Carrier
genericSU2Multiply = Core.multiply GenericSU2.su2GenericGroup

genericSU2Inverse : genericSU2Carrier → genericSU2Carrier
genericSU2Inverse = Core.inverse GenericSU2.su2GenericGroup

genericIdentityIsLegacyIdentity :
  genericSU2Identity ≡ Gauge.unit SU2.su2QuaternionGroup
genericIdentityIsLegacyIdentity = refl

genericMultiplyIsLegacyMultiplyPointwise :
  ∀ a b →
  genericSU2Multiply a b
  ≡ Gauge.multiply SU2.su2QuaternionGroup a b
genericMultiplyIsLegacyMultiplyPointwise a b = refl

genericInverseIsLegacyInversePointwise :
  ∀ a →
  genericSU2Inverse a
  ≡ Gauge.inverse SU2.su2QuaternionGroup a
genericInverseIsLegacyInversePointwise a = refl

-- A legacy GroupStructure assembled from the generic compact-Lie SU(2) law.
-- The extra involutivity field is supplied by the existing concrete quaternion
-- theorem.  The resulting record is definitionally the same concrete law used
-- by the U(1) torus inclusion.
genericSU2AsLegacyGaugeStructure : Gauge.GroupStructure
genericSU2AsLegacyGaugeStructure = record
  { Gauge.GroupStructure.Carrier = genericSU2Carrier
  ; Gauge.GroupStructure.unit = genericSU2Identity
  ; Gauge.GroupStructure.multiply = genericSU2Multiply
  ; Gauge.GroupStructure.inverse = genericSU2Inverse
  ; Gauge.GroupStructure.multiplyAssoc = Core.multiplyAssociative GenericSU2.su2GenericGroup
  ; Gauge.GroupStructure.unitLeft = Core.identityLeft GenericSU2.su2GenericGroup
  ; Gauge.GroupStructure.unitRight = Core.identityRight GenericSU2.su2GenericGroup
  ; Gauge.GroupStructure.inverseLeft = Core.inverseLeft GenericSU2.su2GenericGroup
  ; Gauge.GroupStructure.inverseRight = Core.inverseRight GenericSU2.su2GenericGroup
  ; Gauge.GroupStructure.inverseInvolutive = SU2.su2InverseInvolutive
  }

genericSU2AsLegacyIsCanonicalQuaternionGroup :
  genericSU2AsLegacyGaugeStructure ≡ SU2.su2QuaternionGroup
genericSU2AsLegacyIsCanonicalQuaternionGroup = refl

data SameQuaternionGroupLawAutomaticallyIdentifiesSelectedStructuralGroup : Set where

sameQuaternionLawDoesNotChooseSelectedStructuralGroup :
  SameQuaternionGroupLawAutomaticallyIdentifiesSelectedStructuralGroup → ⊥
sameQuaternionLawDoesNotChooseSelectedStructuralGroup ()

record CasimirQuaternionSU2GroupLawBoundary : Set where
  constructor casimir-quaternion-su2-group-law-boundary
  field
    genericQuaternionSU2GroupOwned : Bool
    legacyQuaternionSU2GaugeGroupOwned : Bool
    genericToLegacyQuaternionGroupLawBridgePaid : Bool
    selectedStructuralGroupIdentifiedWithQuaternionSU2 : Bool

open CasimirQuaternionSU2GroupLawBoundary public

canonicalQuaternionSU2GroupLawBoundary : CasimirQuaternionSU2GroupLawBoundary
canonicalQuaternionSU2GroupLawBoundary =
  casimir-quaternion-su2-group-law-boundary true true true false

quaternionSU2GroupLawBridgeReading : String
quaternionSU2GroupLawBridgeReading =
  "The live CompactLieGroupCore SU(2) group and the legacy Balaban gauge-transport SU(2) GroupStructure are the same concrete unit-quaternion law: same carrier, identity, multiplication and inverse. The adapter is compiler-owned and definitionally equals su2QuaternionGroup. The remaining selected-QFT group payment is therefore not another group-law construction; it is same-object identification of the selected structural compact-simple group with this concrete quaternionic SU(2) group."
