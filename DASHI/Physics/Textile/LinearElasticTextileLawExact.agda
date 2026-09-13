module DASHI.Physics.Textile.LinearElasticTextileLawExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.Textile.TextileMechanicalDimensionExact as TextileDim
import DASHI.Physics.Textile.TextileMechanicalFibreExact as Mechanics

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- Gary Mavko, Tapan Mukerji, Jack Dvorkin,
-- "Elasticity and Hooke's Law", The Rock Physics Handbook, 3rd ed.,
-- Cambridge University Press (2020), chapter DOI:
-- 10.1017/9781108333016.003.
--
-- The source states Hooke's law for isotropic linear elastic material.  This
-- module therefore does NOT make linear elasticity universal for yarn.  It
-- defines a proof-relevant receipt that may be attached only when a producer
-- supplies the corresponding regime-specific constitutive equalities.
------------------------------------------------------------------------

sourceTitle : String
sourceTitle = "Elasticity and Hooke's Law"

sourceDOI : String
sourceDOI = "10.1017/9781108333016.003"

record LinearAxialElasticityReceipt
    (Scalar : Set)
    (state : Mechanics.YarnConstitutiveState Scalar) : Set where
  constructor linear-axial-elasticity-receipt
  field
    multiply : Scalar → Scalar → Scalar

    stressEqualsModulusTimesStrain :
      Dim.magnitude (Mechanics.tensileStress state)
      ≡ multiply
          (Dim.magnitude (Mechanics.youngModulus state))
          (Dim.magnitude (Mechanics.strain state))

    tensionEqualsStressTimesArea :
      Dim.magnitude (Mechanics.tension state)
      ≡ multiply
          (Dim.magnitude (Mechanics.tensileStress state))
          (Dim.magnitude (Mechanics.crossSectionArea state))

open LinearAxialElasticityReceipt public

------------------------------------------------------------------------
-- Dimensional compatibility is discharged independently of the numerical
-- constitutive receipt.  This prevents a scalar equality from smuggling an
-- invalid physical dimension.
------------------------------------------------------------------------

stressLawDimensionallyTyped :
  TextileDim.youngModulusDimension Dim.⊗ᴰ TextileDim.strainDimension
  ≡ TextileDim.stressDimension
stressLawDimensionallyTyped = refl

forceLawDimensionallyTyped :
  TextileDim.stressDimension Dim.⊗ᴰ Dim.areaDimension
  ≡ TextileDim.tensionDimension
forceLawDimensionallyTyped = refl

------------------------------------------------------------------------
-- Non-promotion boundary.
------------------------------------------------------------------------

data EveryYarnStateIsLinearElastic : Set where

everyYarnStateIsNotDeclaredLinearElastic :
  EveryYarnStateIsLinearElastic → ⊥
everyYarnStateIsNotDeclaredLinearElastic ()

data LinearElasticityReceiptDeterminesFailureBehaviour : Set where

linearElasticityReceiptDoesNotDetermineFailureBehaviour :
  LinearElasticityReceiptDeterminesFailureBehaviour → ⊥
linearElasticityReceiptDoesNotDetermineFailureBehaviour ()
