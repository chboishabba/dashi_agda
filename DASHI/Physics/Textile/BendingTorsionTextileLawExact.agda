module DASHI.Physics.Textile.BendingTorsionTextileLawExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer using (+_; -[1+_])

import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.Textile.TextileMechanicalDimensionExact as TextileDim
import DASHI.Physics.Textile.TextileMechanicalFibreExact as Mechanics

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
