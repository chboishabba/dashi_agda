module DASHI.Physics.Textile.KineticSlipEvolutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.Textile.TextileMechanicalDimensionExact as TextileDim
import DASHI.Physics.Textile.QuasiStaticTextileLoadTransferExact as Load
import DASHI.Physics.Textile.FiniteTextileEquilibriumNetworkExact as Network
import DASHI.Physics.Textile.TextileFailureSlipPredicateExact as Predicate

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- OpenStax, University Physics Volume 1:
--   section 6.2 Friction: f_k = mu_k N;
--   section 5.3 Newton's Second Law: F_net = m a.
--
-- This module adds one signed scalar time step after a static-slip threshold
-- has been exceeded.  It is not a full contact integrator, wear law, impact
-- model, or geometric remeshing algorithm.
------------------------------------------------------------------------

frictionSourceTitle : String
frictionSourceTitle = "OpenStax University Physics Volume 1, section 6.2: Friction"

newtonSourceTitle : String
newtonSourceTitle = "OpenStax University Physics Volume 1, section 5.3: Newton's Second Law"

Mass : Set → Set
Mass Scalar = Dim.Quantity Scalar Dim.massDimension

Velocity : Set → Set
Velocity Scalar = Dim.Quantity Scalar Dim.velocityDimension

Acceleration : Set → Set
Acceleration Scalar = Dim.Quantity Scalar Dim.accelerationDimension

TimeStep : Set → Set
TimeStep Scalar = Dim.Quantity Scalar Dim.timeDimension

record KineticSlipEvolutionReceipt
    {Scalar : Set}
    (algebra : Network.OrientedMechanicalAlgebra Scalar)
    (Opposes : Scalar → Scalar → Set)
    (tangentialDemand staticCapacity : Load.Force Scalar) : Set₁ where
  constructor kinetic-slip-evolution-receipt
  field
    staticSlipTriggered :
      Predicate.StaticSlipThresholdExceeded
        (Network.localAlgebra algebra)
        tangentialDemand
        staticCapacity

    normalForce : Load.Force Scalar
    kineticFrictionCoefficient : Load.Coefficient Scalar
    kineticFrictionForce : Load.Force Scalar

    kineticFrictionMagnitudeLaw :
      Load.absoluteValue (Network.localAlgebra algebra)
        (Dim.magnitude kineticFrictionForce)
      ≡ Load.multiply (Network.localAlgebra algebra)
          (Dim.magnitude kineticFrictionCoefficient)
          (Load.absoluteValue (Network.localAlgebra algebra)
            (Dim.magnitude normalForce))

    mass : Mass Scalar
    netForce : Load.Force Scalar
    acceleration : Acceleration Scalar

    newtonSecondLaw :
      Dim.magnitude netForce
      ≡ Load.multiply (Network.localAlgebra algebra)
          (Dim.magnitude mass)
          (Dim.magnitude acceleration)

    velocityBefore : Velocity Scalar
    velocityAfter : Velocity Scalar
    deltaTime : TimeStep Scalar

    velocityUpdate :
      Dim.magnitude velocityAfter
      ≡ Load.add (Network.localAlgebra algebra)
          (Dim.magnitude velocityBefore)
          (Load.multiply (Network.localAlgebra algebra)
            (Dim.magnitude acceleration)
            (Dim.magnitude deltaTime))

    frictionOpposesMotion :
      Opposes
        (Dim.magnitude kineticFrictionForce)
        (Dim.magnitude velocityBefore)

open KineticSlipEvolutionReceipt public

kineticFrictionDimensionallyTyped :
  Dim.dimensionless Dim.⊗ᴰ TextileDim.tensionDimension
  ≡ TextileDim.tensionDimension
kineticFrictionDimensionallyTyped = refl

newtonSecondLawDimensionallyTyped :
  Dim.massDimension Dim.⊗ᴰ Dim.accelerationDimension
  ≡ TextileDim.tensionDimension
newtonSecondLawDimensionallyTyped = refl

velocityUpdateDimensionallyTyped :
  Dim.accelerationDimension Dim.⊗ᴰ Dim.timeDimension
  ≡ Dim.velocityDimension
velocityUpdateDimensionallyTyped = refl

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data OneKineticSlipStepIsCompleteContactDynamics : Set where

oneKineticSlipStepIsNotCompleteContactDynamics :
  OneKineticSlipStepIsCompleteContactDynamics → ⊥
oneKineticSlipStepIsNotCompleteContactDynamics ()

data KineticSlipReceiptDeterminesWearOrDamage : Set where

kineticSlipReceiptDoesNotDetermineWearOrDamage :
  KineticSlipReceiptDeterminesWearOrDamage → ⊥
kineticSlipReceiptDoesNotDetermineWearOrDamage ()
