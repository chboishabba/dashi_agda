module DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact second-order SU(2) jet at the identity.
--
-- We use the unit-quaternion normalization
--
--   exp(t v) = (1 - t² |v|² / 2 , t v) + O(t³).
--
-- Only the linear imaginary coefficient and quadratic real coefficient are
-- required for the normalized real trace.  Their truncated product is exact
-- through order two:
--
--   (r , v) · (s , w) = (r + s - v·w , v + w).
--
-- Here r and s denote coefficients of t² and v,w coefficients of t.
------------------------------------------------------------------------

record Lie3 : Set where
  constructor lie3
  field
    x y z : ℚ

open Lie3 public

lie3Ext : ∀ {a b : Lie3} →
  x a ≡ x b → y a ≡ y b → z a ≡ z b → a ≡ b
lie3Ext {lie3 ax ay az} {lie3 .ax .ay .az} refl refl refl = refl

infixl 20 _+v_
infixl 25 _·v_

_+v_ : Lie3 → Lie3 → Lie3
lie3 ax ay az +v lie3 bx by bz =
  lie3 (ax + bx) (ay + by) (az + bz)

negV : Lie3 → Lie3
negV (lie3 ax ay az) = lie3 (- ax) (- ay) (- az)

_·v_ : Lie3 → Lie3 → ℚ
lie3 ax ay az ·v lie3 bx by bz =
  ax * bx + (ay * by + az * bz)

normSqV : Lie3 → ℚ
normSqV v = v ·v v

half : ℚ
half = + 1 / 2

record SU2SecondJet : Set where
  constructor jet
  field
    realSecond : ℚ
    imaginaryFirst : Lie3

open SU2SecondJet public

identityJet : SU2SecondJet
identityJet = jet 0ℚ (lie3 0ℚ 0ℚ 0ℚ)

exponentialJet : Lie3 → SU2SecondJet
exponentialJet v = jet (- (half * normSqV v)) v

inverseExponentialJet : Lie3 → SU2SecondJet
inverseExponentialJet v = exponentialJet (negV v)

infixl 30 _*j_

_*j_ : SU2SecondJet → SU2SecondJet → SU2SecondJet
jet r v *j jet s w = jet (r + s + (- (v ·v w))) (v +v w)

jetImaginaryFirstMultiply : ∀ a b →
  imaginaryFirst (a *j b)
  ≡ imaginaryFirst a +v imaginaryFirst b
jetImaginaryFirstMultiply (jet r v) (jet s w) = refl

jetRealSecondMultiply : ∀ a b →
  realSecond (a *j b)
  ≡ realSecond a + realSecond b
    + (- (imaginaryFirst a ·v imaginaryFirst b))
jetRealSecondMultiply (jet r v) (jet s w) = refl

------------------------------------------------------------------------
-- The oriented plaquette path
--
--   exp(t a) exp(t b) exp(-t c) exp(-t d)
--
-- has linear Lie-algebra coefficient a+b-c-d.  Its normalized real trace has
-- t² coefficient -|a+b-c-d|²/2.  Consequently the second derivative of
-- 1 - normalizedRealTrace is exactly the squared discrete curl.
------------------------------------------------------------------------

plaquetteJet : Lie3 → Lie3 → Lie3 → Lie3 → SU2SecondJet
plaquetteJet a b c d =
  ((exponentialJet a *j exponentialJet b)
    *j inverseExponentialJet c)
    *j inverseExponentialJet d

plaquetteLinearCurl : Lie3 → Lie3 → Lie3 → Lie3 → Lie3
plaquetteLinearCurl a b c d =
  (a +v b) +v (negV c +v negV d)

plaquetteJetImaginaryFirstExact : ∀ a b c d →
  imaginaryFirst (plaquetteJet a b c d)
  ≡ plaquetteLinearCurl a b c d
plaquetteJetImaginaryFirstExact
  (lie3 ax ay az) (lie3 bx by bz)
  (lie3 cx cy cz) (lie3 dx dy dz) = refl

plaquetteJetRealSecondExact : ∀ a b c d →
  realSecond (plaquetteJet a b c d)
  ≡ - (half * normSqV (plaquetteLinearCurl a b c d))
plaquetteJetRealSecondExact
  (lie3 ax ay az) (lie3 bx by bz)
  (lie3 cx cy cz) (lie3 dx dy dz) =
  ℚRing.solve-∀ ax ay az bx by bz cx cy cz dx dy dz

normalizedRealTraceSecondCoefficient : SU2SecondJet → ℚ
normalizedRealTraceSecondCoefficient = realSecond

wilsonPlaquetteSecondVariation : SU2SecondJet → ℚ
wilsonPlaquetteSecondVariation path =
  - ((+ 2) * normalizedRealTraceSecondCoefficient path)

singlePlaquetteWilsonSecondVariationEqualsCurlNormSq : ∀ a b c d →
  wilsonPlaquetteSecondVariation (plaquetteJet a b c d)
  ≡ normSqV (plaquetteLinearCurl a b c d)
singlePlaquetteWilsonSecondVariationEqualsCurlNormSq
  (lie3 ax ay az) (lie3 bx by bz)
  (lie3 cx cy cz) (lie3 dx dy dz) =
  ℚRing.solve-∀ ax ay az bx by bz cx cy cz dx dy dz

------------------------------------------------------------------------
-- Reverse orientation sends the curl to its negative and therefore preserves
-- the Wilson Hessian.  This is the algebraic content needed by the configured
-- six-positive-plane convention.
------------------------------------------------------------------------

reversePlaquetteLinearCurl : Lie3 → Lie3 → Lie3 → Lie3 → Lie3
reversePlaquetteLinearCurl a b c d =
  plaquetteLinearCurl d c b a

reverseCurlIsNegative : ∀ a b c d →
  reversePlaquetteLinearCurl a b c d
  ≡ negV (plaquetteLinearCurl a b c d)
reverseCurlIsNegative
  (lie3 ax ay az) (lie3 bx by bz)
  (lie3 cx cy cz) (lie3 dx dy dz) =
  lie3Ext
    (ℚRing.solve-∀ ax bx cx dx)
    (ℚRing.solve-∀ ay by cy dy)
    (ℚRing.solve-∀ az bz cz dz)

reverseOrientationPreservesCurlNormSq : ∀ a b c d →
  normSqV (reversePlaquetteLinearCurl a b c d)
  ≡ normSqV (plaquetteLinearCurl a b c d)
reverseOrientationPreservesCurlNormSq
  (lie3 ax ay az) (lie3 bx by bz)
  (lie3 cx cy cz) (lie3 dx dy dz) =
  ℚRing.solve-∀ ax ay az bx by bz cx cy cz dx dy dz

su2WilsonPlaquetteSecondJetLevel : ProofLevel
su2WilsonPlaquetteSecondJetLevel = machineChecked

singlePlaquetteWilsonSecondVariationLevel : ProofLevel
singlePlaquetteWilsonSecondVariationLevel = machineChecked
