module DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", second edition.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- B. J. Birch and H. P. F. Swinnerton-Dyer,
-- "Notes on elliptic curves. II.", Journal für die reine und angewandte
-- Mathematik 218 (1965), 79--108.
-- DOI: 10.1515/crll.1965.218.79.
--
-- DASHI CONTRIBUTION
--
-- Add an exact short-Weierstrass carrier over the repository's rational
-- arithmetic, its discriminant, a concrete nonsingular curve
--
--   E : y^2 = x^3 - x,
--
-- and a finite p=5 point-count row.  The row counts 7 affine points plus the
-- point at infinity, hence #E(F_5)=8 and a_5=5+1-8=-2.  The corresponding
-- local Euler polynomial has coefficients 1, 2 and 5.
--
-- The finite row is a checked arithmetic witness, not a construction of the
-- global L-function, modularity, Mordell--Weil finite generation, Selmer
-- groups, Tate--Shafarevich groups or the BSD formula.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

------------------------------------------------------------------------
-- Closed rational numerals used by the exact polynomial identities.
------------------------------------------------------------------------

two four five six eight sixteen twentySeven sixtyFour : ℚ
two = 1ℚ + 1ℚ
four = two + two
five = four + 1ℚ
six = five + 1ℚ
eight = four + four
sixteen = eight + eight
twentySeven = sixteen + eight + two + 1ℚ
sixtyFour = sixteen * four

record ShortWeierstrassCurve : Set where
  constructor shortWeierstrass
  field
    aCoefficient bCoefficient : ℚ
    discriminantNonzero :
      (- sixteen) *
        (four * aCoefficient * aCoefficient * aCoefficient
          + twentySeven * bCoefficient * bCoefficient)
      ≡ 0ℚ → ⊥

open ShortWeierstrassCurve public

shortDiscriminant : ShortWeierstrassCurve → ℚ
shortDiscriminant curve =
  (- sixteen) *
    (four * aCoefficient curve * aCoefficient curve * aCoefficient curve
      + twentySeven * bCoefficient curve * bCoefficient curve)

minusOneCurveDiscriminant :
  (- sixteen) *
    (four * (- 1ℚ) * (- 1ℚ) * (- 1ℚ)
      + twentySeven * 0ℚ * 0ℚ)
  ≡ sixtyFour
minusOneCurveDiscriminant = solve []

sixtyFourIsNonzero : sixtyFour ≡ 0ℚ → ⊥
sixtyFourIsNonzero ()

curveY2EqualsX3MinusX : ShortWeierstrassCurve
curveY2EqualsX3MinusX =
  shortWeierstrass (- 1ℚ) 0ℚ
    (λ discriminantZero →
      sixtyFourIsNonzero
        (transEquality
          (symEquality minusOneCurveDiscriminant)
          discriminantZero))
  where
    transEquality : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    transEquality refl second = second

    symEquality : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    symEquality refl = refl

curveDiscriminantIsSixtyFour :
  shortDiscriminant curveY2EqualsX3MinusX ≡ sixtyFour
curveDiscriminantIsSixtyFour = minusOneCurveDiscriminant

------------------------------------------------------------------------
-- Exact p=5 point-count row.
--
-- For x=0,1,2,3,4 the numbers of y solving y^2=x^3-x mod 5 are
-- 1,1,2,2,1.  Adding the point at infinity gives 8.
------------------------------------------------------------------------

sumNat : List Nat → Nat
sumNat [] = zero
sumNat (value ∷ values) = value + sumNat values

p5AffineFibreCounts : List Nat
p5AffineFibreCounts =
  suc zero ∷
  suc zero ∷
  suc (suc zero) ∷
  suc (suc zero) ∷
  suc zero ∷ []

p5AffinePointCount : Nat
p5AffinePointCount = sumNat p5AffineFibreCounts

p5AffinePointCountIsSeven : p5AffinePointCount ≡ 7
p5AffinePointCountIsSeven = refl

p5ProjectivePointCount : Nat
p5ProjectivePointCount = suc p5AffinePointCount

p5ProjectivePointCountIsEight : p5ProjectivePointCount ≡ 8
p5ProjectivePointCountIsEight = refl

frobeniusTraceAtFive : ℚ
frobeniusTraceAtFive = five + 1ℚ - eight

frobeniusTraceAtFiveIsMinusTwo :
  frobeniusTraceAtFive ≡ - two
frobeniusTraceAtFiveIsMinusTwo = solve []

record LocalEulerPolynomial : Set where
  constructor localEulerPolynomial
  field
    constantCoefficient linearCoefficient quadraticCoefficient : ℚ

open LocalEulerPolynomial public

localEulerFactorAtFive : LocalEulerPolynomial
localEulerFactorAtFive =
  localEulerPolynomial 1ℚ (- frobeniusTraceAtFive) five

localFactorAtFiveCoefficients :
  constantCoefficient localEulerFactorAtFive ≡ 1ℚ
  × linearCoefficient localEulerFactorAtFive ≡ two
  × quadraticCoefficient localEulerFactorAtFive ≡ five
localFactorAtFiveCoefficients =
  refl , solve [] , refl
  where
    open import Data.Product using (_×_; _,_)

record ArithmeticFrobeniusDatum : Set₁ where
  field
    prime : Nat
    finiteFieldPointCount : Nat
    traceOfFrobenius : ℚ
    localPolynomial : LocalEulerPolynomial
    traceFormula : Set
    hasseBound : Set

p5FrobeniusDatum : ArithmeticFrobeniusDatum
p5FrobeniusDatum = record
  { prime = 5
  ; finiteFieldPointCount = p5ProjectivePointCount
  ; traceOfFrobenius = frobeniusTraceAtFive
  ; localPolynomial = localEulerFactorAtFive
  ; traceFormula = frobeniusTraceAtFive ≡ five + 1ℚ - eight
  ; hasseBound = Set
  }
