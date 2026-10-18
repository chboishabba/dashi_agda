module DASHI.Physics.Foundations.CMP119CurvatureWilsonF2SingleFamilyCompilerValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.CMP119CurvatureWilsonF2SingleFamilyCompilerExact as Cut

secondFiniteCurvatureFamilyRetired :
  Cut.independentFiniteF2CurvatureFamilyRequired ≡ false
secondFiniteCurvatureFamilyRetired = refl

sameFamilyPaysWilsonAndF2 :
  Cut.sameCurvatureFamilyPaysWilsonTenSlotDSAndF2 ≡ true
sameFamilyPaysWilsonAndF2 = refl

f2PointwiseNonnegativityInherited :
  Cut.f2PointwiseNonnegativityNeedsNewPhysics ≡ false
f2PointwiseNonnegativityInherited = refl

strictPositivityStillNeedsWitness :
  Cut.strictF2PositivityStillNeedsSelectedNonzeroCurvatureWitness ≡ true
strictPositivityStillNeedsWitness = refl
