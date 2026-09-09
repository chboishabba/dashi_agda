module DASHI.Physics.Textile.QuasiStaticTextileLoadTransferExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.Textile.TextileMechanicalDimensionExact as TextileDim
import DASHI.Physics.Textile.TextileMechanicalFibreExact as Mechanics
import DASHI.Physics.Textile.StitchPhysicalFibreBridgeExact as Physical

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- Static friction source:
-- OpenStax, University Physics Volume 1, section 6.2 "Friction".
-- The source states the standard static-friction bound
--
--   f_s <= mu_s N
--
-- with equality at the limiting static-friction threshold.
--
-- This module deliberately remains one-dimensional and quasi-static.  It
-- supplies local signed axial-force balance and a proof-bearing static-friction
-- gate.  It is not a full rod, shell, contact, or 3-D continuum solver.
------------------------------------------------------------------------

frictionSourceTitle : String
frictionSourceTitle = "University Physics Volume 1, section 6.2: Friction"

record ScalarMechanicalAlgebra (Scalar : Set) : Set₁ where
  constructor scalar-mechanical-algebra
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar
    multiply : Scalar → Scalar → Scalar
    absoluteValue : Scalar → Scalar
    _≤_ : Scalar → Scalar → Set

open ScalarMechanicalAlgebra public

Force : Set → Set
Force Scalar = Dim.Quantity Scalar TextileDim.tensionDimension

Coefficient : Set → Set
Coefficient Scalar = Dim.Quantity Scalar Dim.dimensionless

------------------------------------------------------------------------
-- One-dimensional signed force equilibrium.
--
-- incoming + external = outgoing
--
-- Signs are carried by Scalar.  A producer is responsible for choosing a
-- signed scalar convention appropriate to its local tangent coordinate.
------------------------------------------------------------------------

record LocalAxialForceBalance
    {Scalar : Set}
    (algebra : ScalarMechanicalAlgebra Scalar) : Set where
  constructor local-axial-force-balance
  field
    incomingForce : Force Scalar
    externalForce : Force Scalar
    outgoingForce : Force Scalar

    equilibrium :
      add algebra
        (Dim.magnitude incomingForce)
        (Dim.magnitude externalForce)
      ≡ Dim.magnitude outgoingForce

open LocalAxialForceBalance public

------------------------------------------------------------------------
-- Static friction admissibility.
--
-- frictionCapacity = mu_s * N
-- |tangentialDemand| <= |frictionCapacity|
------------------------------------------------------------------------

record StaticFrictionReceipt
    {Scalar : Set}
    (algebra : ScalarMechanicalAlgebra Scalar) : Set where
  constructor static-friction-receipt
  field
    tangentialDemand : Force Scalar
    normalForce : Force Scalar
    staticFrictionCoefficient : Coefficient Scalar
    frictionCapacity : Force Scalar

    capacityLaw :
      Dim.magnitude frictionCapacity
      ≡ multiply algebra
          (Dim.magnitude staticFrictionCoefficient)
          (Dim.magnitude normalForce)

    noSlip :
      _≤_ algebra
        (absoluteValue algebra (Dim.magnitude tangentialDemand))
        (absoluteValue algebra (Dim.magnitude frictionCapacity))

open StaticFrictionReceipt public

frictionCapacityDimensionallyTyped :
  Dim.dimensionless Dim.⊗ᴰ TextileDim.tensionDimension
  ≡ TextileDim.tensionDimension
frictionCapacityDimensionallyTyped = refl

------------------------------------------------------------------------
-- Load-redistribution receipt.
--
-- This is the first bridge from a before/after mechanical transition to an
-- actual local physics obligation: the supplied after-fibre must come with a
-- local equilibrium witness and, when a contact is claimed to remain stuck,
-- an explicit static-friction receipt.
------------------------------------------------------------------------

record QuasiStaticLoadRedistributionReceipt
    {Scalar : Set}
    (algebra : ScalarMechanicalAlgebra Scalar)
    (before after : Physical.StitchMechanicalFibre Scalar) : Set₁ where
  constructor quasi-static-load-redistribution-receipt
  field
    balance : LocalAxialForceBalance algebra
    contact : StaticFrictionReceipt algebra
    retainedBeforeFibre : Physical.StitchMechanicalFibre Scalar
    retainedAfterFibre : Physical.StitchMechanicalFibre Scalar
    beforeIsRetained : retainedBeforeFibre ≡ before
    afterIsRetained : retainedAfterFibre ≡ after

open QuasiStaticLoadRedistributionReceipt public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data OneDimensionalBalanceIsFullThreeDimensionalTextileMechanics : Set where

oneDimensionalBalanceIsNotFullThreeDimensionalTextileMechanics :
  OneDimensionalBalanceIsFullThreeDimensionalTextileMechanics → ⊥
oneDimensionalBalanceIsNotFullThreeDimensionalTextileMechanics ()

data StaticFrictionReceiptDeterminesDynamicSlipEvolution : Set where

staticFrictionReceiptDoesNotDetermineDynamicSlipEvolution :
  StaticFrictionReceiptDeterminesDynamicSlipEvolution → ⊥
staticFrictionReceiptDoesNotDetermineDynamicSlipEvolution ()

data LocalBalanceDeterminesGlobalFabricEquilibrium : Set where

localBalanceDoesNotDetermineGlobalFabricEquilibrium :
  LocalBalanceDeterminesGlobalFabricEquilibrium → ⊥
localBalanceDoesNotDetermineGlobalFabricEquilibrium ()
