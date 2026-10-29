module DASHI.Foundations.PolynomialC3S3RationalCharacterAlgebraExact where

-- Classical Reynolds/character decomposition, made explicit on the already
-- owned 11 C3 conjugation classes and seven S3 classes.
-- Historical authority: Burnside, Reynolds, Maschke/finite representation
-- theory. DASHI owns only this finite typed construction.
-- Uses rational coefficients; NOT F3, trit-valued averaging, an orthogonal
-- Hilbert projection, Monster 3B, or the free output-phase action.
-- No postulates; exact-head Agda kernel verification remains pending.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; 0ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Foundations.PolynomialC3S3TwentySevenOrbitQuotientExact as Q

-- C2 on the 11 C3 orbit classes comes from the original S3 reflection.
-- Two rational-valued coordinates per swapped pair admit a canonical
-- symmetric / antisymmetric separation without a second quotient ontology.

Field11ℚ : Set
Field11ℚ = Q.Orbit11 → ℚ

reflect : Field11ℚ → Field11ℚ
reflect f o = f (Q.reflectionOn11 o)

reflectInvolutive : (f : Field11ℚ) (o : Q.Orbit11) →
  reflect (reflect f) o ≡ f o
reflectInvolutive f o = cong f (Q.reflection11Involutive o)

-- The unnormalised character operators are definable even without division:
-- E(f)=f+s.f and O(f)=f-s.f. Actual normalized Reynolds projectors are
-- obtained by dividing by 2 in characteristic zero, a separate analytic
-- implementation obligation.

evenNumerator : Field11ℚ → Field11ℚ
evenNumerator f o = f o + reflect f o

oddNumerator : Field11ℚ → Field11ℚ
oddNumerator f o = f o - reflect f o

-- Non-promotion: these constructors alone do not assert orthogonality
-- or numerical efficiency. Group-action and rational-addition proof laws
-- are left to the existing canonical rational algebra owner.
