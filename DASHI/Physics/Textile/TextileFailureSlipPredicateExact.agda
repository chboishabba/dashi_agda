module DASHI.Physics.Textile.TextileFailureSlipPredicateExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.Textile.TextileMechanicalFibreExact as Mechanics
import DASHI.Physics.Textile.QuasiStaticTextileLoadTransferExact as Load

------------------------------------------------------------------------
-- Predicate layer only.
--
-- These types classify a supplied mechanical state relative to its supplied
-- thresholds.  They do not compute those thresholds, do not update geometry,
-- and do not claim a universal yarn failure model.
------------------------------------------------------------------------

record TensileSafe
    {Scalar : Set}
    (algebra : Load.ScalarMechanicalAlgebra Scalar)
    (state : Mechanics.YarnConstitutiveState Scalar) : Set where
  constructor tensile-safe
  field
    stressWithinFailureThreshold :
      Load._≤_ algebra
        (Load.absoluteValue algebra
          (Dim.magnitude (Mechanics.tensileStress state)))
        (Load.absoluteValue algebra
          (Dim.magnitude (Mechanics.failureStress state)))

open TensileSafe public

record TensileThresholdExceeded
    {Scalar : Set}
    (algebra : Load.ScalarMechanicalAlgebra Scalar)
    (state : Mechanics.YarnConstitutiveState Scalar) : Set where
  constructor tensile-threshold-exceeded
  field
    notWithinFailureThreshold :
      Load._≤_ algebra
        (Load.absoluteValue algebra
          (Dim.magnitude (Mechanics.tensileStress state)))
        (Load.absoluteValue algebra
          (Dim.magnitude (Mechanics.failureStress state)))
      → ⊥

open TensileThresholdExceeded public

record StaticContactSticks
    {Scalar : Set}
    (algebra : Load.ScalarMechanicalAlgebra Scalar)
    (contact : Load.StaticFrictionReceipt algebra) : Set where
  constructor static-contact-sticks
  field
    staticAdmissibility :
      Load._≤_ algebra
        (Load.absoluteValue algebra
          (Dim.magnitude (Load.tangentialDemand contact)))
        (Load.absoluteValue algebra
          (Dim.magnitude (Load.frictionCapacity contact)))

open StaticContactSticks public

canonicalStaticContactSticks :
  {Scalar : Set}
  {algebra : Load.ScalarMechanicalAlgebra Scalar} →
  (contact : Load.StaticFrictionReceipt algebra) →
  StaticContactSticks algebra contact
canonicalStaticContactSticks contact =
  static-contact-sticks (Load.noSlip contact)

record StaticSlipThresholdExceeded
    {Scalar : Set}
    (algebra : Load.ScalarMechanicalAlgebra Scalar)
    (tangentialDemand frictionCapacity : Load.Force Scalar) : Set where
  constructor static-slip-threshold-exceeded
  field
    demandNotWithinCapacity :
      Load._≤_ algebra
        (Load.absoluteValue algebra (Dim.magnitude tangentialDemand))
        (Load.absoluteValue algebra (Dim.magnitude frictionCapacity))
      → ⊥

open StaticSlipThresholdExceeded public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data ThresholdExceededDeterminesFracturePath : Set where

thresholdExceededDoesNotDetermineFracturePath :
  ThresholdExceededDeterminesFracturePath → ⊥
thresholdExceededDoesNotDetermineFracturePath ()

data SlipThresholdExceededDeterminesKineticFrictionTrajectory : Set where

slipThresholdExceededDoesNotDetermineKineticFrictionTrajectory :
  SlipThresholdExceededDeterminesKineticFrictionTrajectory → ⊥
slipThresholdExceededDoesNotDetermineKineticFrictionTrajectory ()

data LocalSafetyImpliesGlobalFabricSafety : Set where

localSafetyDoesNotImplyGlobalFabricSafety :
  LocalSafetyImpliesGlobalFabricSafety → ⊥
localSafetyDoesNotImplyGlobalFabricSafety ()
