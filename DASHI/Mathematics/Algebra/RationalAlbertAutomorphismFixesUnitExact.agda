module DASHI.Mathematics.Algebra.RationalAlbertAutomorphismFixesUnitExact where

------------------------------------------------------------------------
-- EVERY ACTUAL JORDAN AUTOMORPHISM FIXES THE DISTINGUISHED UNIT
--
-- This is an internal same-carrier theorem, not an F4 classification claim.
-- If f is bijective and preserves the Jordan product, choose b=f^{-1}(1).
-- Then
--
--   f(1) ∘ 1 = f(1) ∘ f(b) = f(1 ∘ b) = f(b) = 1.
--
-- Since 1 is also the right unit, f(1) ∘ 1 = f(1), hence f(1)=1.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J
import DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact as Laws
import DASHI.Mathematics.Algebra.RationalAlbertAutomorphismClosureExact as Aut

open Aut.AlbertAutomorphism

automorphismFixesUnit :
  (automorphism : Aut.AlbertAutomorphism) →
  forward automorphism A.unitAlbert ≡ A.unitAlbert
automorphismFixesUnit automorphism = sym unitEqualsImage
  where
    preimageUnit : A.RationalAlbert
    preimageUnit = backward automorphism A.unitAlbert

    unitEqualsImage : A.unitAlbert ≡ forward automorphism A.unitAlbert
    unitEqualsImage
      rewrite Laws.jordanLeftUnit preimageUnit
            | forwardBackward automorphism A.unitAlbert
            | Laws.jordanRightUnit (forward automorphism A.unitAlbert)
      = preservesJordan automorphism A.unitAlbert preimageUnit
