module DASHI.Mathematics.Arithmetic.EisensteinAZeroEllipticScalarExtensionExact where

------------------------------------------------------------------------
-- A=0 SHORT-WEIERSTRASS CURVES -> EISENSTEIN SCALAR EXTENSION
--
-- This owner pays a narrow same-object seam already available from repository
-- carriers.  It does NOT identify the short-Weierstrass `a=0` family with
-- `j=0` by theorem, nor construct complex multiplication, a Hecke character or
-- an elliptic L-function.
--
-- Given
--
--   y^2 = x^3 + B
--
-- over the repo's rational short-Weierstrass carrier, the canonical embedding
-- q |-> q + 0*omega sends the same equation into the existing exact rational
-- Eisenstein carrier.  The already-proved omega action then preserves that
-- scalar-extended cubic.  The action does not in general restrict to the
-- rational image: omega*1 = omega is not q+0*omega for any rational q.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
import Relation.Binary.PropositionalEquality as Eq

import DASHI.Biology.EisensteinNineRingInterferenceExact as E
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EisensteinJZeroCubicSymmetryExact as Cubic

------------------------------------------------------------------------
-- 1. Canonical rational scalar embedding into the same Eisenstein carrier.
------------------------------------------------------------------------

embedQ : ℚ → E.Eisenstein
embedQ q = E.eisenstein q 0ℚ

embedQInjective : ∀ {a b} → embedQ a ≡ embedQ b → a ≡ b
embedQInjective equality = Eq.cong E.realCoordinate equality

embedAdd : (a b : ℚ) →
  E.add (embedQ a) (embedQ b) ≡ embedQ (a + b)
embedAdd a b =
  Cubic.ext
    (ℚRing.solve-∀ a b)
    (ℚRing.solve-∀ a b)

embedMul : (a b : ℚ) →
  E.multiply (embedQ a) (embedQ b) ≡ embedQ (a * b)
embedMul a b =
  Cubic.ext
    (ℚRing.solve-∀ a b)
    (ℚRing.solve-∀ a b)

embedSquare : (q : ℚ) →
  Cubic.square (embedQ q) ≡ embedQ (q * q)
embedSquare q = embedMul q q

embedCube : (q : ℚ) →
  Cubic.cube (embedQ q) ≡ embedQ (q * (q * q))
embedCube q =
  Eq.trans
    (Eq.cong (E.multiply (embedQ q)) (embedMul q q))
    (embedMul q (q * q))

embedCubicRhs : (B x : ℚ) →
  E.add (Cubic.cube (embedQ x)) (embedQ B)
  ≡ embedQ (x * (x * x) + B)
embedCubicRhs B x =
  Eq.trans
    (Eq.cong (λ cubic → E.add cubic (embedQ B)) (embedCube x))
    (embedAdd (x * (x * x)) B)

------------------------------------------------------------------------
-- 2. Same equation before and after scalar extension.
------------------------------------------------------------------------

OnRationalAZeroCubic : ℚ → ℚ → ℚ → Set
OnRationalAZeroCubic B x y =
  y * y ≡ x * (x * x) + B

rationalAZeroCubicEmbeds :
  ∀ {B x y} →
  OnRationalAZeroCubic B x y →
  Cubic.OnJZeroCubic (embedQ B) (embedQ x) (embedQ y)
rationalAZeroCubicEmbeds {B} {x} {y} onCurve =
  Eq.trans
    (embedSquare y)
    (Eq.trans
      (Eq.cong embedQ onCurve)
      (Eq.sym (embedCubicRhs B x)))

embeddedAZeroCubicReflects :
  ∀ {B x y} →
  Cubic.OnJZeroCubic (embedQ B) (embedQ x) (embedQ y) →
  OnRationalAZeroCubic B x y
embeddedAZeroCubicReflects {B} {x} {y} onCurve =
  embedQInjective
    (Eq.trans
      (Eq.sym (embedSquare y))
      (Eq.trans onCurve (embedCubicRhs B x)))

------------------------------------------------------------------------
-- 3. Weld to the repository short-Weierstrass carrier when a=0.
------------------------------------------------------------------------

OnShortWeierstrass :
  Elliptic.ShortWeierstrassCurve → ℚ → ℚ → Set
OnShortWeierstrass curve x y =
  y * y
  ≡ x * (x * x)
    + Elliptic.aCoefficient curve * x
    + Elliptic.bCoefficient curve

aZeroRhsCollapse :
  ∀ {curve} (x : ℚ) →
  Elliptic.aCoefficient curve ≡ 0ℚ →
  x * (x * x)
    + Elliptic.aCoefficient curve * x
    + Elliptic.bCoefficient curve
  ≡ x * (x * x) + Elliptic.bCoefficient curve
aZeroRhsCollapse {curve} x refl =
  ℚRing.solve-∀ x (Elliptic.bCoefficient curve)

aZeroShortPointToRationalCubic :
  ∀ {curve x y} →
  Elliptic.aCoefficient curve ≡ 0ℚ →
  OnShortWeierstrass curve x y →
  OnRationalAZeroCubic (Elliptic.bCoefficient curve) x y
aZeroShortPointToRationalCubic {curve} {x} aZero onCurve =
  Eq.trans onCurve (aZeroRhsCollapse x aZero)

rationalCubicToAZeroShortPoint :
  ∀ {curve x y} →
  Elliptic.aCoefficient curve ≡ 0ℚ →
  OnRationalAZeroCubic (Elliptic.bCoefficient curve) x y →
  OnShortWeierstrass curve x y
rationalCubicToAZeroShortPoint {curve} {x} aZero onCurve =
  Eq.trans onCurve (Eq.sym (aZeroRhsCollapse x aZero))

aZeroShortPointEmbeds :
  ∀ {curve x y} →
  Elliptic.aCoefficient curve ≡ 0ℚ →
  OnShortWeierstrass curve x y →
  Cubic.OnJZeroCubic
    (embedQ (Elliptic.bCoefficient curve))
    (embedQ x)
    (embedQ y)
aZeroShortPointEmbeds aZero onCurve =
  rationalAZeroCubicEmbeds
    (aZeroShortPointToRationalCubic aZero onCurve)

embeddedCubicReflectsAZeroShortPoint :
  ∀ {curve x y} →
  Elliptic.aCoefficient curve ≡ 0ℚ →
  Cubic.OnJZeroCubic
    (embedQ (Elliptic.bCoefficient curve))
    (embedQ x)
    (embedQ y) →
  OnShortWeierstrass curve x y
embeddedCubicReflectsAZeroShortPoint aZero onCurve =
  rationalCubicToAZeroShortPoint aZero
    (embeddedAZeroCubicReflects onCurve)

aZeroShortPointIffEmbedded :
  ∀ {curve x y} →
  (aZero : Elliptic.aCoefficient curve ≡ 0ℚ) →
  (OnShortWeierstrass curve x y →
    Cubic.OnJZeroCubic
      (embedQ (Elliptic.bCoefficient curve))
      (embedQ x)
      (embedQ y))
  ×
  (Cubic.OnJZeroCubic
      (embedQ (Elliptic.bCoefficient curve))
      (embedQ x)
      (embedQ y) →
    OnShortWeierstrass curve x y)
aZeroShortPointIffEmbedded aZero =
  aZeroShortPointEmbeds aZero ,
  embeddedCubicReflectsAZeroShortPoint aZero

------------------------------------------------------------------------
-- 4. The existing C3 action acts on the scalar-extended same cubic.
------------------------------------------------------------------------

omegaActionPreservesEmbeddedAZeroPoint :
  ∀ {curve x y} →
  (aZero : Elliptic.aCoefficient curve ≡ 0ℚ) →
  OnShortWeierstrass curve x y →
  Cubic.OnJZeroCubic
    (embedQ (Elliptic.bCoefficient curve))
    (Cubic.rotateX (embedQ x))
    (embedQ y)
omegaActionPreservesEmbeddedAZeroPoint aZero onCurve =
  Cubic.omegaXPreservesJZeroCubic
    (aZeroShortPointEmbeds aZero onCurve)

------------------------------------------------------------------------
-- 5. The C3 action does not generally restrict to rational scalars.
------------------------------------------------------------------------

zeroNotOne : 0ℚ ≡ E.qOne → ⊥
zeroNotOne ()

omegaNotEmbedded :
  (q : ℚ) → E.omega ≡ embedQ q → ⊥
omegaNotEmbedded q equality =
  zeroNotOne
    (Eq.sym (Eq.cong E.omegaCoordinate equality))

rotateEmbeddedOneIsOmega :
  Cubic.rotateX (embedQ E.qOne) ≡ E.omega
rotateEmbeddedOneIsOmega =
  Cubic.ext
    (ℚRing.solve [])
    (ℚRing.solve [])

rotateEmbeddedOneNotEmbedded :
  (q : ℚ) →
  Cubic.rotateX (embedQ E.qOne) ≡ embedQ q →
  ⊥
rotateEmbeddedOneNotEmbedded q equality =
  omegaNotEmbedded q
    (Eq.trans (Eq.sym rotateEmbeddedOneIsOmega) equality)

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record EisensteinAZeroEllipticScalarExtensionBoundary : Set where
  constructor eisenstein-a-zero-elliptic-scalar-extension-boundary
  field
    rationalScalarEmbeddingPaid : Bool
    aZeroPointSameObjectBridgePaid : Bool
    c3ActionOnEisensteinScalarExtensionPaid : Bool
    c3ActionRestrictsToRationalEmbedding : Bool
    jInvariantZeroFormulaPaid : Bool
    fullCMEndomorphismRingPaid : Bool
    heckeCharacterPaid : Bool
    ellipticLSeriesIdentifiedWithChiMinus3 : Bool

open EisensteinAZeroEllipticScalarExtensionBoundary public

canonicalBoundary : EisensteinAZeroEllipticScalarExtensionBoundary
canonicalBoundary =
  eisenstein-a-zero-elliptic-scalar-extension-boundary
    true
    true
    true
    false
    false
    false
    false
    false
