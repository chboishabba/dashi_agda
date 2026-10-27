module DASHI.Physics.Foundations.TorqueTrialectic369ConsumerRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.TorqueTrialectic369Exact as Torque
import DASHI.Physics.Foundations.TorqueTrialectic369NestedExact as Nested
import DASHI.Physics.Foundations.ResonantFlightPhaseCoupledPowerExact as Flight
import DASHI.Physics.POAMSScientificMechanismBoundaryExact as POAMS
import DASHI.Physics.Textile.BendingTorsionTextileLawExact as Textile
import DASHI.Physics.Textile.TextileMechanicalFibreExact as Mechanics

------------------------------------------------------------------------
-- The three pre-existing torque lanes preserve their original torque values
-- while attaching the common 369 / pants / C3 geometry.
------------------------------------------------------------------------

textileConsumerPreservesTorque :
  ∀ {Scalar : Set}
    {state : Mechanics.YarnConstitutiveState Scalar}
    (voxel : Torque.BracketVoxel)
    (receipt : Textile.BendingTorsionConstitutiveReceipt Scalar state) →
  Torque.value (Textile.textileOrientedTorque voxel receipt)
  ≡ Textile.torque receipt
textileConsumerPreservesTorque voxel receipt = refl

resonantConsumerPreservesTorque :
  (power : Flight.PhaseCoupledPower) →
  (geometry : Flight.Phase power → Torque.BracketVoxel) →
  (phase : Flight.Phase power) →
  Torque.value (Flight.phaseOrientedTorque power geometry phase)
  ≡ Flight.torque power phase
resonantConsumerPreservesTorque power geometry phase = refl

angularMomentumConsumerPreservesTorque :
  ∀ {TorqueValue : Set}
    (voxel : Torque.BracketVoxel)
    (value : TorqueValue) →
  Torque.value
    (POAMS.orientedTorque
      (POAMS.attachAngularMomentumTorque voxel value))
  ≡ value
angularMomentumConsumerPreservesTorque voxel value = refl

------------------------------------------------------------------------
-- Nested trialectic specialization keeps the mature T9 -> T18 structure.
------------------------------------------------------------------------

nestedTorqueDialecticIsT9 :
  Nested.torqueDialecticStateCount ≡ 19683
nestedTorqueDialecticIsT9 =
  Nested.torqueDialecticStateCountIsT9

nestedTorqueBoundaryIsT18 :
  Nested.torqueBoundaryCoordinateCount ≡ 18
nestedTorqueBoundaryIsT18 =
  Nested.torqueBoundaryCoordinateCountIsEighteen
