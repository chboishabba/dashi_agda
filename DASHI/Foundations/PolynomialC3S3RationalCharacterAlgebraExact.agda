module DASHI.Foundations.PolynomialC3S3RationalCharacterAlgebraExact where

-- Thin SAME-CARRIER adapter. Existing rational C2 projector mathematics belongs
-- to DASHI.Biology.MoonshineOrbifoldSectorProjectorExact (and historical
-- finite-group representation theory). This file owns only the eleven-orbit
-- reflection instantiation. No reassignment of prior DASHI/Ibrahim ownership.
-- Source-written; Agda kernel verification pending; not yet a TOE import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong)
import DASHI.Foundations.PolynomialC3S3TwentySevenOrbitQuotientExact as Q
import DASHI.Biology.MoonshineOrbifoldSectorProjectorExact as Existing

Field11ℚ : Set
Field11ℚ = Q.Orbit11 → ℚ

reflect : Field11ℚ → Field11ℚ
reflect f o = f (Q.reflectionOn11 o)

reflectInvolutive : (f : Field11ℚ) (o : Q.Orbit11) →
  reflect (reflect f) o ≡ f o
reflectInvolutive f o = cong f (Q.reflection11Involutive o)

-- Construct the actual pair that the established rational C2 projector
-- already operates upon. No duplicate addition/subtraction/ring proof.
reflectionPair : Field11ℚ → Q.Orbit11 → Existing.RationalPair
reflectionPair f o =
  Existing.pair (f o) (f (Q.reflectionOn11 o))

positiveProjectionAt : Field11ℚ → Q.Orbit11 → ℚ
positiveProjectionAt f o =
  Existing.first (Existing.positiveProjection (reflectionPair f o))

negativeProjectionAt : Field11ℚ → Q.Orbit11 → ℚ
negativeProjectionAt f o =
  Existing.first (Existing.negativeProjection (reflectionPair f o))

-- Reuses the ACTUAL prior rational-solver theorem, not an equivalent
-- source-written arithmetic reimplementation.
reflectionPositiveNegativeReconstruct :
  (f : Field11ℚ) (o : Q.Orbit11) →
  Data.Rational.Base._+_
    (positiveProjectionAt f o) (negativeProjectionAt f o)
  ≡ f o
reflectionPositiveNegativeReconstruct f o =
  Existing.positivePlusNegativeFirst (reflectionPair f o)

-- Reflection exchanges the two coordinates of this prior-owned pair.
reflectionPairSwap :
  (f : Field11ℚ) (o : Q.Orbit11) →
  reflectionPair f (Q.reflectionOn11 o)
    ≡ Existing.swap (reflectionPair f o)
reflectionPairSwap f o
  rewrite Q.reflection11Involutive o = Agda.Builtin.Equality.refl
