module DASHI.Physics.Textile.BendingTorsionTextileLawExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer using (+_; -[1+_])

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.Textile.TextileMechanicalDimensionExact as TextileDim
import DASHI.Physics.Textile.TextileMechanicalFibreExact as Mechanics
import DASHI.Physics.Foundations.TorqueTrialectic369Exact as Torque369

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- Bending:
-- MIT OpenCourseWare, 2.080J Structural Mechanics, Lecture 4,
-- "Development of Constitutive Equations", Eq. (4.27): M = E I kappa.
--
-- Torsion:
-- MIT OpenCourseWare, Unified Engineering Materials & Structures handout,
-- torsion of round shafts: T = G J d(phi)/dx.
--
-- These are slender-member constitutive laws under their respective modelling
-- assumptions.  They are conditional receipts here, not universal yarn laws.
------------------------------------------------------------------------

bendingSourceTitle : String
bendingSourceTitle = "MIT 2.080J Structural Mechanics Lecture 4: Development of Constitutive Equations"

torsionSourceTitle : String
torsionSourceTitle = "MIT Unified Engineering Materials and Structures: Torsion of Round Shafts"

momentDimension : Dim.MechanicalDimension
momentDimension =
  Dim.dimension (+ (suc zero)) (+ (suc (suc zero))) -[1+ suc zero ]

twistRateDimension : Dim.MechanicalDimension
twistRateDimension = Dim.inverseLengthDimension

Moment : Set → Set
Moment Scalar = Dim.Quantity Scalar momentDimension

Curvature : Set → Set
Curvature Scalar = Dim.Quantity Scalar TextileDim.curvatureDimension

TwistRate : Set → Set
TwistRate Scalar = Dim.Quantity Scalar twistRateDimension

record BendingTorsionConstitutiveReceipt
    (Scalar : Set)
    (state : Mechanics.YarnConstitutiveState Scalar) : Set where
  constructor bending-torsion-constitutive-receipt
  field
    multiply : Scalar → Scalar → Scalar

    curvature : Curvature Scalar
    bendingMoment : Moment Scalar

    bendingMomentLaw :
      Dim.magnitude bendingMoment
      ≡ multiply
          (Dim.magnitude (Mechanics.bendingRigidity state))
          (Dim.magnitude curvature)

    twistRate : TwistRate Scalar
    torque : Moment Scalar

    torsionLaw :
      Dim.magnitude torque
      ≡ multiply
          (Dim.magnitude (Mechanics.torsionalRigidity state))
          (Dim.magnitude twistRate)

open BendingTorsionConstitutiveReceipt public

bendingLawDimensionallyTyped :
  TextileDim.bendingRigidityDimension Dim.⊗ᴰ TextileDim.curvatureDimension
  ≡ momentDimension
bendingLawDimensionallyTyped = refl

torsionLawDimensionallyTyped :
  TextileDim.torsionalRigidityDimension Dim.⊗ᴰ twistRateDimension
  ≡ momentDimension
torsionLawDimensionallyTyped = refl

------------------------------------------------------------------------
-- Shared torque geometry.
--
-- The constitutive scalar law remains exactly T = G J phi'.  A caller that
-- knows the local output/lever/force axes may attach the same torque value to
-- the canonical 369 / pants / C3 torque carrier without changing its units or
-- magnitude semantics.
------------------------------------------------------------------------

textileOrientedTorque :
  ∀ {Scalar : Set}
    {state : Mechanics.YarnConstitutiveState Scalar} →
  Torque369.BracketVoxel →
  BendingTorsionConstitutiveReceipt Scalar state →
  Torque369.OrientedTorque (Moment Scalar)
textileOrientedTorque voxel receipt =
  Torque369.oriented-torque voxel (torque receipt)

textileTorqueMagnitudeWitness :
  ∀ {Scalar : Set}
    {state : Mechanics.YarnConstitutiveState Scalar}
    (voxel : Torque369.BracketVoxel)
    (receipt : BendingTorsionConstitutiveReceipt Scalar state) →
  Torque369.TorqueMagnitudeWitness
    Scalar
    (Moment Scalar)
    (textileOrientedTorque voxel receipt)
textileTorqueMagnitudeWitness voxel receipt =
  Torque369.torque-magnitude-witness
    Dim.magnitude
    (Dim.magnitude (torque receipt))
    refl

textileTorqueOrientation :
  ∀ {Scalar : Set}
    {state : Mechanics.YarnConstitutiveState Scalar} →
  (voxel : Torque369.BracketVoxel) →
  (receipt : BendingTorsionConstitutiveReceipt Scalar state) →
  BT.Trit
textileTorqueOrientation voxel receipt =
  Torque369.orientedTorqueOrientation
    (textileOrientedTorque voxel receipt)

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data EveryYarnStateObeysEulerBernoulliBending : Set where

everyYarnStateIsNotDeclaredEulerBernoulli :
  EveryYarnStateObeysEulerBernoulliBending → ⊥
everyYarnStateIsNotDeclaredEulerBernoulli ()

data EveryYarnStateObeysSaintVenantTorsion : Set where

everyYarnStateIsNotDeclaredSaintVenantTorsion :
  EveryYarnStateObeysSaintVenantTorsion → ⊥
everyYarnStateIsNotDeclaredSaintVenantTorsion ()

data BendingTorsionReceiptDeterminesFailureEvolution : Set where

bendingTorsionReceiptDoesNotDetermineFailureEvolution :
  BendingTorsionReceiptDeterminesFailureEvolution → ⊥
bendingTorsionReceiptDoesNotDetermineFailureEvolution ()
