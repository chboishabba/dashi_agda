module DASHI.Mathematics.Arithmetic.EisensteinJZeroCubicSymmetryExact where

------------------------------------------------------------------------
-- EISENSTEIN ORDER-THREE SYMMETRY OF THE j=0-TYPE CUBIC FAMILY
--
-- On the exact rational Eisenstein carrier, the affine cubic family
--
--   y^2 = x^3 + B
--
-- is preserved by x |-> omega*x because omega^3 = 1.  This is the exact local
-- algebraic symmetry underlying the familiar CM-by-Z[omega] story for j=0
-- elliptic curves.  This module proves only that same-object cubic symmetry;
-- it does not manufacture a global elliptic-curve group law, a Hecke character,
-- modularity, an L-function, or any BSD conjecture inhabitant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import Data.Rational.Tactic.RingSolver as ℚRing
import Relation.Binary.PropositionalEquality as Eq

import DASHI.Biology.EisensteinNineRingInterferenceExact as E

square : E.Eisenstein → E.Eisenstein
square z = E.multiply z z

cube : E.Eisenstein → E.Eisenstein
cube z = E.multiply z (E.multiply z z)

rotateX : E.Eisenstein → E.Eisenstein
rotateX x = E.multiply E.omega x

rotateXSquared : E.Eisenstein → E.Eisenstein
rotateXSquared x = E.multiply E.omegaSquared x

ext :
  ∀ {left right : E.Eisenstein} →
  E.realCoordinate left ≡ E.realCoordinate right →
  E.omegaCoordinate left ≡ E.omegaCoordinate right →
  left ≡ right
ext {E.eisenstein _ _} {E.eisenstein _ _} refl refl = refl

------------------------------------------------------------------------
-- Cubic invariance of the two nontrivial C3 actions.
------------------------------------------------------------------------

omegaScaleCubeInvariant :
  (x : E.Eisenstein) → cube (rotateX x) ≡ cube x
omegaScaleCubeInvariant (E.eisenstein xr xo) =
  ext
    (ℚRing.solve-∀ xr xo)
    (ℚRing.solve-∀ xr xo)

omegaSquaredScaleCubeInvariant :
  (x : E.Eisenstein) → cube (rotateXSquared x) ≡ cube x
omegaSquaredScaleCubeInvariant (E.eisenstein xr xo) =
  ext
    (ℚRing.solve-∀ xr xo)
    (ℚRing.solve-∀ xr xo)

rotateXThree :
  (x : E.Eisenstein) →
  rotateX (rotateX (rotateX x)) ≡ x
rotateXThree (E.eisenstein xr xo) =
  ext
    (ℚRing.solve-∀ xr xo)
    (ℚRing.solve-∀ xr xo)

------------------------------------------------------------------------
-- Affine cubic predicate and exact same-object preservation theorem.
------------------------------------------------------------------------

OnJZeroCubic : E.Eisenstein → E.Eisenstein → E.Eisenstein → Set
OnJZeroCubic B x y = square y ≡ E.add (cube x) B

omegaXPreservesJZeroCubic :
  ∀ {B x y} →
  OnJZeroCubic B x y →
  OnJZeroCubic B (rotateX x) y
omegaXPreservesJZeroCubic {B} {x} {y} onCurve =
  Eq.trans
    onCurve
    (Eq.sym
      (Eq.cong (λ cubic → E.add cubic B)
        (omegaScaleCubeInvariant x)))

omegaSquaredXPreservesJZeroCubic :
  ∀ {B x y} →
  OnJZeroCubic B x y →
  OnJZeroCubic B (rotateXSquared x) y
omegaSquaredXPreservesJZeroCubic {B} {x} {y} onCurve =
  Eq.trans
    onCurve
    (Eq.sym
      (Eq.cong (λ cubic → E.add cubic B)
        (omegaSquaredScaleCubeInvariant x)))

------------------------------------------------------------------------
-- Exact finite action package.
------------------------------------------------------------------------

record EisensteinCubicC3Action (B : E.Eisenstein) : Set₁ where
  field
    action : E.Eisenstein → E.Eisenstein
    actionCubed : ∀ x → action (action (action x)) ≡ x
    preservesCubic :
      ∀ {x y} → OnJZeroCubic B x y → OnJZeroCubic B (action x) y

omegaCubicC3Action :
  (B : E.Eisenstein) → EisensteinCubicC3Action B
omegaCubicC3Action B = record
  { action = rotateX
  ; actionCubed = rotateXThree
  ; preservesCubic = omegaXPreservesJZeroCubic
  }

------------------------------------------------------------------------
-- Promotion boundary toward CM/BSD/Hodge.
------------------------------------------------------------------------

data LocalCubicC3SymmetryIsFullComplexMultiplicationTheory : Set where

data LocalCubicC3SymmetryConstructsHeckeCharacter : Set where

data LocalCubicC3SymmetryProvesBSD : Set where

data LocalCubicC3SymmetryProvesGeneralHodge : Set where

noAutomaticCMTheory :
  LocalCubicC3SymmetryIsFullComplexMultiplicationTheory → ⊥
noAutomaticCMTheory ()

noAutomaticHeckeCharacter :
  LocalCubicC3SymmetryConstructsHeckeCharacter → ⊥
noAutomaticHeckeCharacter ()

noAutomaticBSD : LocalCubicC3SymmetryProvesBSD → ⊥
noAutomaticBSD ()

noAutomaticHodge : LocalCubicC3SymmetryProvesGeneralHodge → ⊥
noAutomaticHodge ()
