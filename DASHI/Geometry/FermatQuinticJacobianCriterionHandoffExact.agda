module DASHI.Geometry.FermatQuinticJacobianCriterionHandoffExact where

-- Same-object handoff from the existing algebraic nonvanishing proof to
-- the projective Jacobian criterion. The Jacobian criterion itself is
-- supplied as a mathematical theorem, not fabricated by a Bool flag.
-- Smoothness of the chosen Fermat projective hypersurface follows once
-- the criterion and concrete characteristic-zero field are instantiated.

open import Data.Empty using (⊥)
open import Agda.Builtin.Equality using (_≡_)
import DASHI.Geometry.FermatQuinticGradientNonvanishingExact as Fermat
import DASHI.Geometry.QuinticThreefoldCandidate as Target

record ProjectiveJacobianCriterion (F : Fermat.QuinticField) : Set₁ where
  field
    SmoothAt : Fermat.ProjectiveFiveCoordinates F → Set
    criterion :
      (z : Fermat.ProjectiveFiveCoordinates F) →
      (Fermat.QuinticGradientZero F z → ⊥) →
      SmoothAt z

open ProjectiveJacobianCriterion public

fermatSmoothAtEveryProjectivePoint :
  (F : Fermat.QuinticField) →
  (criterion : ProjectiveJacobianCriterion F) →
  (z : Fermat.ProjectiveFiveCoordinates F) →
  SmoothAt criterion z
fermatSmoothAtEveryProjectivePoint F criterion z =
  ProjectiveJacobianCriterion.criterion criterion z
    (Fermat.fermatQuinticHasNoSimultaneousGradientZero F z)

-- Name and dimension agree with the existing selected Fermat model.
selectedComplexDimensionIsThree :
  Target.hypersurfaceComplexDimension Target.quinticThreefoldCandidate
    ≡ 3
selectedComplexDimensionIsThree = Target.quinticComplexDimensionIsThree
