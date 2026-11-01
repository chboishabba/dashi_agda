module DASHI.Moonshine.Monster3BFiniteHeisenbergPermutationExact where

------------------------------------------------------------------------
-- Constructive inverse laws for the six translation generators used by the
-- finite-Heisenberg Schrodinger model.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (neg; zer; pos)
open import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact using
  (X6; x6; Axis6; axis0; axis1; axis2; axis3; axis4; axis5;
   translate; translateInverse)

translateInverseAfterTranslate :
  (axis : Axis6) → (state : X6) →
  translateInverse axis (translate axis state) ≡ state
translateInverseAfterTranslate axis0 (x6 neg a1 a2 a3 a4 a5) = refl
translateInverseAfterTranslate axis0 (x6 zer a1 a2 a3 a4 a5) = refl
translateInverseAfterTranslate axis0 (x6 pos a1 a2 a3 a4 a5) = refl
translateInverseAfterTranslate axis1 (x6 a0 neg a2 a3 a4 a5) = refl
translateInverseAfterTranslate axis1 (x6 a0 zer a2 a3 a4 a5) = refl
translateInverseAfterTranslate axis1 (x6 a0 pos a2 a3 a4 a5) = refl
translateInverseAfterTranslate axis2 (x6 a0 a1 neg a3 a4 a5) = refl
translateInverseAfterTranslate axis2 (x6 a0 a1 zer a3 a4 a5) = refl
translateInverseAfterTranslate axis2 (x6 a0 a1 pos a3 a4 a5) = refl
translateInverseAfterTranslate axis3 (x6 a0 a1 a2 neg a4 a5) = refl
translateInverseAfterTranslate axis3 (x6 a0 a1 a2 zer a4 a5) = refl
translateInverseAfterTranslate axis3 (x6 a0 a1 a2 pos a4 a5) = refl
translateInverseAfterTranslate axis4 (x6 a0 a1 a2 a3 neg a5) = refl
translateInverseAfterTranslate axis4 (x6 a0 a1 a2 a3 zer a5) = refl
translateInverseAfterTranslate axis4 (x6 a0 a1 a2 a3 pos a5) = refl
translateInverseAfterTranslate axis5 (x6 a0 a1 a2 a3 a4 neg) = refl
translateInverseAfterTranslate axis5 (x6 a0 a1 a2 a3 a4 zer) = refl
translateInverseAfterTranslate axis5 (x6 a0 a1 a2 a3 a4 pos) = refl

translateAfterTranslateInverse :
  (axis : Axis6) → (state : X6) →
  translate axis (translateInverse axis state) ≡ state
translateAfterTranslateInverse axis0 (x6 neg a1 a2 a3 a4 a5) = refl
translateAfterTranslateInverse axis0 (x6 zer a1 a2 a3 a4 a5) = refl
translateAfterTranslateInverse axis0 (x6 pos a1 a2 a3 a4 a5) = refl
translateAfterTranslateInverse axis1 (x6 a0 neg a2 a3 a4 a5) = refl
translateAfterTranslateInverse axis1 (x6 a0 zer a2 a3 a4 a5) = refl
translateAfterTranslateInverse axis1 (x6 a0 pos a2 a3 a4 a5) = refl
translateAfterTranslateInverse axis2 (x6 a0 a1 neg a3 a4 a5) = refl
translateAfterTranslateInverse axis2 (x6 a0 a1 zer a3 a4 a5) = refl
translateAfterTranslateInverse axis2 (x6 a0 a1 pos a3 a4 a5) = refl
translateAfterTranslateInverse axis3 (x6 a0 a1 a2 neg a4 a5) = refl
translateAfterTranslateInverse axis3 (x6 a0 a1 a2 zer a4 a5) = refl
translateAfterTranslateInverse axis3 (x6 a0 a1 a2 pos a4 a5) = refl
translateAfterTranslateInverse axis4 (x6 a0 a1 a2 a3 neg a5) = refl
translateAfterTranslateInverse axis4 (x6 a0 a1 a2 a3 zer a5) = refl
translateAfterTranslateInverse axis4 (x6 a0 a1 a2 a3 pos a5) = refl
translateAfterTranslateInverse axis5 (x6 a0 a1 a2 a3 a4 neg) = refl
translateAfterTranslateInverse axis5 (x6 a0 a1 a2 a3 a4 zer) = refl
translateAfterTranslateInverse axis5 (x6 a0 a1 a2 a3 a4 pos) = refl
