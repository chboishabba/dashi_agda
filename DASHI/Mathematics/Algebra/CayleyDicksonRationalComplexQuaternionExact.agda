module DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John C. Baez,
-- "The Octonions", Bulletin of the American Mathematical Society 39 (2002),
-- 145--205.
-- DOI: 10.1090/S0273-0979-01-00934-X.
--
-- Aleksandra Galecka,
-- "A Proof of the Hurwitz Theorem About Composition Algebras".
-- DOI: 10.24917/20809751.13.4.
--
-- DASHI CONTRIBUTION
--
-- Reuse the exact rational quaternion carrier already used by the Yang--Mills
-- Wilson-Hessian development and identify it literally with one
-- Cayley--Dickson doubling of rational complex numbers.  The convention is
--
--   (a,b)(c,d) = (ac - conjugate(d)b , da + b conjugate(c)).
--
-- The coordinate theorem below proves that this multiplication is exactly the
-- repository quaternion multiplication, not merely isomorphic by an unnamed
-- external theorem.  It also proves complex and quaternion norm composition
-- over the exact rational carrier.
--
-- This module does not claim the real analytic division property, positivity
-- over R, the full Hurwitz classification, octonion alternativity, or any
-- theorem beyond the displayed finite polynomial identities.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

------------------------------------------------------------------------
-- Rational complex algebra.
------------------------------------------------------------------------

record RationalComplex : Set where
  constructor complex
  field
    re im : ℚ

open RationalComplex public

zeroC oneC : RationalComplex
zeroC = complex 0ℚ 0ℚ
oneC  = complex 1ℚ 0ℚ

_+c_ : RationalComplex → RationalComplex → RationalComplex
complex a b +c complex c d = complex (a + c) (b + d)

_-c_ : RationalComplex → RationalComplex → RationalComplex
complex a b -c complex c d = complex (a - c) (b - d)

negC : RationalComplex → RationalComplex
negC (complex a b) = complex (- a) (- b)

_*c_ : RationalComplex → RationalComplex → RationalComplex
complex a b *c complex c d =
  complex (a * c - b * d) (a * d + b * c)

conjugateC : RationalComplex → RationalComplex
conjugateC (complex a b) = complex a (- b)

complexNormSq : RationalComplex → ℚ
complexNormSq (complex a b) = a * a + b * b

complexExt :
  ∀ {left right} →
  re left ≡ re right → im left ≡ im right → left ≡ right
complexExt {complex _ _} {complex _ _} refl refl = refl

complexConjugateInvolutive : ∀ value →
  conjugateC (conjugateC value) ≡ value
complexConjugateInvolutive (complex a b) =
  complexExt (solve (a ∷ [])) (solve (b ∷ []))

complexConjugateReversesProduct : ∀ left right →
  conjugateC (left *c right)
  ≡ conjugateC right *c conjugateC left
complexConjugateReversesProduct
    (complex a b) (complex c d) =
  complexExt
    (solve (a ∷ b ∷ c ∷ d ∷ []))
    (solve (a ∷ b ∷ c ∷ d ∷ []))

complexNormMultiplicative : ∀ left right →
  complexNormSq (left *c right)
  ≡ complexNormSq left * complexNormSq right
complexNormMultiplicative
    (complex a b) (complex c d) =
  solve (a ∷ b ∷ c ∷ d ∷ [])

------------------------------------------------------------------------
-- One Cayley--Dickson doubling.
------------------------------------------------------------------------

record ComplexPair : Set where
  constructor pairC
  field
    first second : RationalComplex

open ComplexPair public

cayleyDicksonMultiply : ComplexPair → ComplexPair → ComplexPair
cayleyDicksonMultiply (pairC a b) (pairC c d) =
  pairC
    ((a *c c) -c (conjugateC d *c b))
    ((d *c a) +c (b *c conjugateC c))

cayleyDicksonConjugate : ComplexPair → ComplexPair
cayleyDicksonConjugate (pairC a b) =
  pairC (conjugateC a) (negC b)

cayleyDicksonNormSq : ComplexPair → ℚ
cayleyDicksonNormSq (pairC a b) =
  complexNormSq a + complexNormSq b

------------------------------------------------------------------------
-- Literal equivalence with the existing rational quaternion carrier.
------------------------------------------------------------------------

doubleToQuaternion : ComplexPair → Q.RationalQuaternion
doubleToQuaternion
    (pairC (complex a0 a1) (complex a2 a3)) =
  Q.quat a0 a1 a2 a3

quaternionToDouble : Q.RationalQuaternion → ComplexPair
quaternionToDouble (Q.quat a0 a1 a2 a3) =
  pairC (complex a0 a1) (complex a2 a3)

quaternionDoubleRoundTrip : ∀ value →
  doubleToQuaternion (quaternionToDouble value) ≡ value
quaternionDoubleRoundTrip (Q.quat a0 a1 a2 a3) = refl

doubleQuaternionRoundTrip : ∀ value →
  quaternionToDouble (doubleToQuaternion value) ≡ value
doubleQuaternionRoundTrip
    (pairC (complex a0 a1) (complex a2 a3)) = refl

cayleyDicksonMultiplyMatchesQuaternion : ∀ left right →
  doubleToQuaternion (cayleyDicksonMultiply left right)
  ≡ Q._*q_ (doubleToQuaternion left) (doubleToQuaternion right)
cayleyDicksonMultiplyMatchesQuaternion
    (pairC (complex a0 a1) (complex a2 a3))
    (pairC (complex b0 b1) (complex b2 b3)) =
  Q.quaternionExt
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ []))
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ []))
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ []))
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ []))

quaternionConjugate : Q.RationalQuaternion → Q.RationalQuaternion
quaternionConjugate (Q.quat a0 a1 a2 a3) =
  Q.quat a0 (- a1) (- a2) (- a3)

quaternionNormSq : Q.RationalQuaternion → ℚ
quaternionNormSq (Q.quat a0 a1 a2 a3) =
  a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3

cayleyDicksonConjugateMatchesQuaternion : ∀ value →
  doubleToQuaternion (cayleyDicksonConjugate value)
  ≡ quaternionConjugate (doubleToQuaternion value)
cayleyDicksonConjugateMatchesQuaternion
    (pairC (complex a0 a1) (complex a2 a3)) =
  Q.quaternionExt
    (solve (a0 ∷ []))
    (solve (a1 ∷ []))
    (solve (a2 ∷ []))
    (solve (a3 ∷ []))

cayleyDicksonNormMatchesQuaternion : ∀ value →
  cayleyDicksonNormSq value
  ≡ quaternionNormSq (doubleToQuaternion value)
cayleyDicksonNormMatchesQuaternion
    (pairC (complex a0 a1) (complex a2 a3)) =
  solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ [])

quaternionConjugateInvolutive : ∀ value →
  quaternionConjugate (quaternionConjugate value) ≡ value
quaternionConjugateInvolutive (Q.quat a0 a1 a2 a3) =
  Q.quaternionExt
    (solve (a0 ∷ []))
    (solve (a1 ∷ []))
    (solve (a2 ∷ []))
    (solve (a3 ∷ []))

quaternionConjugateReversesProduct : ∀ left right →
  quaternionConjugate (Q._*q_ left right)
  ≡ Q._*q_ (quaternionConjugate right) (quaternionConjugate left)
quaternionConjugateReversesProduct
    (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3) =
  Q.quaternionExt
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ []))
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ []))
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ []))
    (solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ []))

quaternionNormMultiplicative : ∀ left right →
  quaternionNormSq (Q._*q_ left right)
  ≡ quaternionNormSq left * quaternionNormSq right
quaternionNormMultiplicative
    (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3) =
  solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ [])

cayleyDicksonNormMultiplicative : ∀ left right →
  cayleyDicksonNormSq (cayleyDicksonMultiply left right)
  ≡ cayleyDicksonNormSq left * cayleyDicksonNormSq right
cayleyDicksonNormMultiplicative
    (pairC (complex a0 a1) (complex a2 a3))
    (pairC (complex b0 b1) (complex b2 b3)) =
  solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ [])

quaternionUnitNormProduct : ∀ left right →
  quaternionNormSq left ≡ 1ℚ →
  quaternionNormSq right ≡ 1ℚ →
  quaternionNormSq (Q._*q_ left right) ≡ 1ℚ
quaternionUnitNormProduct left right leftUnit rightUnit
  rewrite quaternionNormMultiplicative left right
        | leftUnit | rightUnit =
  solve []
