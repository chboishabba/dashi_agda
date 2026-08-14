module DASHI.Cognition.PNF.OrientedZeroKoopmanMatrixExact where

------------------------------------------------------------------------
-- ORIENTED-ZERO CANONICAL QUOTIENT AS AN EXACT 4D LINEAR SYSTEM
--
-- SOURCE-FACING MOTIVATION
-- Steven L. Brunton, Bingni W. Brunton, Joshua L. Proctor, J. Nathan Kutz,
-- "Koopman Invariant Subspaces and Finite Linear Representations of Nonlinear
-- Dynamical Systems for Control", PLOS ONE 11(2): e0150171 (2016).
-- DOI: 10.1371/journal.pone.0150171.
--
-- The four canonical future classes of Wave4 are encoded as the four standard
-- basis vectors over Q.  The state pushforward is a 0--1 linear map, while the
-- observable Koopman pullback is its transpose action.  Their pairing is exact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact as Wave

record Vec4 : Set where
  constructor vec4
  field
    x0 x1 x2 x3 : ℚ

open Vec4 public

zeroV : Vec4
zeroV = vec4 0ℚ 0ℚ 0ℚ 0ℚ

_+V_ : Vec4 → Vec4 → Vec4
vec4 a b c d +V vec4 e f g h =
  vec4 (a + e) (b + f) (c + g) (d + h)

scaleV : ℚ → Vec4 → Vec4
scaleV s (vec4 a b c d) = vec4 (s * a) (s * b) (s * c) (s * d)

record Vec4PointwiseEqual (left right : Vec4) : Set where
  constructor vec4PointwiseEqual
  field
    equal0 : x0 left ≡ x0 right
    equal1 : x1 left ≡ x1 right
    equal2 : x2 left ≡ x2 right
    equal3 : x3 left ≡ x3 right

open Vec4PointwiseEqual public

basis0 basis1 basis2 basis3 : Vec4
basis0 = vec4 1ℚ 0ℚ 0ℚ 0ℚ
basis1 = vec4 0ℚ 1ℚ 0ℚ 0ℚ
basis2 = vec4 0ℚ 0ℚ 1ℚ 0ℚ
basis3 = vec4 0ℚ 0ℚ 0ℚ 1ℚ

oneHot : Wave.Wave4 → Vec4
oneHot Wave.negativeOne = basis0
oneHot Wave.negativeZero = basis1
oneHot Wave.positiveZero = basis2
oneHot Wave.positiveOne = basis3

------------------------------------------------------------------------
-- State pushforward matrix for
--   -1 -> -0 -> +0 -> +1 -> +1.
-- In column-vector form the matrix has columns e1,e2,e3,e3.
------------------------------------------------------------------------

pushWave : Vec4 → Vec4
pushWave (vec4 a b c d) = vec4 0ℚ a b (c + d)

pushWaveOneHotIntertwines : (state : Wave.Wave4) →
  pushWave (oneHot state) ≡ oneHot (Wave.waveStep state)
pushWaveOneHotIntertwines Wave.negativeOne = refl
pushWaveOneHotIntertwines Wave.negativeZero = refl
pushWaveOneHotIntertwines Wave.positiveZero = refl
pushWaveOneHotIntertwines Wave.positiveOne = refl

pushWaveAdditive : (left right : Vec4) →
  Vec4PointwiseEqual
    (pushWave (left +V right))
    (pushWave left +V pushWave right)
pushWaveAdditive (vec4 a b c d) (vec4 e f g h) =
  vec4PointwiseEqual solve-∀ solve-∀ solve-∀ solve-∀

pushWaveHomogeneous : (scalar : ℚ) (vector : Vec4) →
  Vec4PointwiseEqual
    (pushWave (scaleV scalar vector))
    (scaleV scalar (pushWave vector))
pushWaveHomogeneous scalar (vec4 a b c d) =
  vec4PointwiseEqual solve-∀ solve-∀ solve-∀ solve-∀

------------------------------------------------------------------------
-- Observable pullback (Koopman matrix):
--   K f(x) = f(waveStep x).
-- Thus [a,b,c,d] -> [b,c,d,d].
------------------------------------------------------------------------

pullWave : Vec4 → Vec4
pullWave (vec4 a b c d) = vec4 b c d d

observableVector : (Wave.Wave4 → ℚ) → Vec4
observableVector f = vec4
  (f Wave.negativeOne)
  (f Wave.negativeZero)
  (f Wave.positiveZero)
  (f Wave.positiveOne)

pullWaveIsKoopman : (f : Wave.Wave4 → ℚ) →
  pullWave (observableVector f)
  ≡ observableVector (λ state → f (Wave.waveStep state))
pullWaveIsKoopman f = refl

pullWaveAdditive : (left right : Vec4) →
  Vec4PointwiseEqual
    (pullWave (left +V right))
    (pullWave left +V pullWave right)
pullWaveAdditive (vec4 a b c d) (vec4 e f g h) =
  vec4PointwiseEqual refl refl refl refl

pullWaveHomogeneous : (scalar : ℚ) (vector : Vec4) →
  Vec4PointwiseEqual
    (pullWave (scaleV scalar vector))
    (scaleV scalar (pullWave vector))
pullWaveHomogeneous scalar (vec4 a b c d) =
  vec4PointwiseEqual refl refl refl refl

------------------------------------------------------------------------
-- Pushforward / pullback duality.
------------------------------------------------------------------------

dot : Vec4 → Vec4 → ℚ
dot (vec4 a b c d) (vec4 e f g h) =
  a * e + b * f + c * g + d * h

pushPullDuality : (stateMass observable : Vec4) →
  dot (pushWave stateMass) observable
  ≡ dot stateMass (pullWave observable)
pushPullDuality (vec4 a b c d) (vec4 e f g h) = solve-∀

------------------------------------------------------------------------
-- The four canonical indicator coordinates are independent in the strongest
-- coordinatewise sense: a linear combination of the four basis vectors is
-- literally the coefficient vector.  Hence zero combination exposes every
-- coefficient as zero.
------------------------------------------------------------------------

linearCombinationOfBasis : ℚ → ℚ → ℚ → ℚ → Vec4
linearCombinationOfBasis a b c d =
  scaleV a basis0 +V
  (scaleV b basis1 +V (scaleV c basis2 +V scaleV d basis3))

basisCombinationIsCoefficientVector : (a b c d : ℚ) →
  linearCombinationOfBasis a b c d ≡ vec4 a b c d
basisCombinationIsCoefficientVector a b c d = refl

record CoefficientsZero (a b c d : ℚ) : Set where
  constructor coefficientsZero
  field
    aZero : a ≡ 0ℚ
    bZero : b ≡ 0ℚ
    cZero : c ≡ 0ℚ
    dZero : d ≡ 0ℚ

basisIndependent : (a b c d : ℚ) →
  linearCombinationOfBasis a b c d ≡ zeroV →
  CoefficientsZero a b c d
basisIndependent a b c d refl =
  coefficientsZero refl refl refl refl

------------------------------------------------------------------------
-- Boundary: this proves a natural exact 4D indicator/full-observable realization
-- of the four-state canonical quotient.  It does NOT prove that every injective
-- nonlinear embedding of four discrete states needs ambient dimension four.
-- Dimension minimality requires fixing a linear realization class/basis notion.
------------------------------------------------------------------------
