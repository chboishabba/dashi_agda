module DASHI.Mathematics.Algebra.RationalAlbertLinearExceptionalGroupsExact where

------------------------------------------------------------------------
-- LINEAR EXCEPTIONAL-GROUP TARGETS ON THE ACTUAL RATIONAL ALBERT MODULE
--
-- The older `AlbertAutomorphism` compiler is intentionally lightweight: it
-- records bijectivity plus Jordan/cubic preservation, but not linearity as a
-- field.  The algebraic-group statements for E6 and F4 require the genuine
-- 27-dimensional linear module.  This owner therefore types the correct
-- objects explicitly on the SAME RationalAlbert carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J

record LinearBijection : Set where
  field
    forward backward : A.RationalAlbert → A.RationalAlbert
    backwardForward : (x : A.RationalAlbert) → backward (forward x) ≡ x
    forwardBackward : (x : A.RationalAlbert) → forward (backward x) ≡ x
    preservesAdd : (x y : A.RationalAlbert) →
      forward (A._+A_ x y) ≡ A._+A_ (forward x) (forward y)
    preservesScale : (q : ℚ) → (x : A.RationalAlbert) →
      forward (A.scaleA q x) ≡ A.scaleA q (forward x)
open LinearBijection public

record CubicLinearSymmetry : Set where
  field
    linear : LinearBijection
    preservesCubic : (x : A.RationalAlbert) →
      A.cubicNorm (forward linear x) ≡ A.cubicNorm x
open CubicLinearSymmetry public

record JordanLinearAutomorphism : Set where
  field
    cubicLinear : CubicLinearSymmetry
    preservesJordan : (x y : A.RationalAlbert) →
      forward (linear cubicLinear) (J.jordanProduct x y)
      ≡ J.jordanProduct
          (forward (linear cubicLinear) x)
          (forward (linear cubicLinear) y)
open JordanLinearAutomorphism public

fixesUnit : CubicLinearSymmetry → Set
fixesUnit symmetry =
  forward (linear symmetry) A.unitAlbert ≡ A.unitAlbert

record UnitStabilizingCubicSymmetry : Set where
  field
    symmetry : CubicLinearSymmetry
    unitFixed : fixesUnit symmetry
open UnitStabilizingCubicSymmetry public

------------------------------------------------------------------------
-- Exact recognition target.
--
-- Classically, for an Albert algebra in characteristic 0:
--   * the relevant cubic-norm linear symmetry group is of type E6;
--   * the unit stabilizer / Jordan automorphism group is of type F4.
-- The field/form-sensitive theorem is represented as a same-carrier contract,
-- not inferred here from dimensions or finite weight orbits.
------------------------------------------------------------------------

record E6F4SameCarrierRecognition : Set₁ where
  field
    E6Group : Set
    F4Group : Set
    e6Action : E6Group → A.RationalAlbert → A.RationalAlbert
    f4Action : F4Group → A.RationalAlbert → A.RationalAlbert

    e6ActionLinearCubicProperty : Set
    e6ActionLinearCubic : e6ActionLinearCubicProperty

    f4ActionJordanProperty : Set
    f4ActionJordan : f4ActionJordanProperty

    f4EmbedsInE6Property : Set
    f4EmbedsInE6 : f4EmbedsInE6Property

    f4IsUnitStabilizerProperty : Set
    f4IsUnitStabilizer : f4IsUnitStabilizerProperty

    e6TypeRecognitionProperty : Set
    e6TypeRecognition : e6TypeRecognitionProperty

    f4TypeRecognitionProperty : Set
    f4TypeRecognition : f4TypeRecognitionProperty

open E6F4SameCarrierRecognition public
