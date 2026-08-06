module DASHI.Mathematics.Arithmetic.EllipticCurveFiniteTwoDescentSeedExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", second edition.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- DASHI CONTRIBUTION
--
-- Build an exact finite 2-descent seed for the rational two-torsion subgroup
-- of E : y^2=x^3-x.  The four torsion codes form C2 x C2.  Their finite
-- Kummer-code target is another C2 x C2, and the map is the coordinatewise
-- identity.  The map is a homomorphism, injective, surjective and has trivial
-- kernel; all four images are enumerated.
--
-- This is the finite algebraic seed beneath 2-descent.  Square classes in
-- Q*/Q*2, local solubility at every place, the global Selmer group, the image
-- of E(Q)/2E(Q), and the Tate--Shafarevich quotient remain separate arithmetic
-- obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Arithmetic.EllipticCurveTwoTorsionAndBadPrimeExact as Torsion

record SquareClassPair : Set where
  constructor squareClassPair
  field
    firstSquareClass secondSquareClass : Torsion.Bit

open SquareClassPair public

squareClassExtensionality : ∀ {left right} →
  firstSquareClass left ≡ firstSquareClass right →
  secondSquareClass left ≡ secondSquareClass right →
  left ≡ right
squareClassExtensionality
    {squareClassPair _ _} {squareClassPair _ _} refl refl = refl

zeroSquareClass : SquareClassPair
zeroSquareClass = squareClassPair Torsion.bit0 Torsion.bit0

addSquareClass : SquareClassPair → SquareClassPair → SquareClassPair
addSquareClass
    (squareClassPair first second)
    (squareClassPair first' second') =
  squareClassPair
    (Torsion.xor first first')
    (Torsion.xor second second')

finiteKummerMap : Torsion.TwoTorsionCode → SquareClassPair
finiteKummerMap point =
  squareClassPair (Torsion.firstBit point) (Torsion.secondBit point)

finiteKummerHomomorphism : ∀ left right →
  finiteKummerMap (Torsion.addTorsion left right)
  ≡ addSquareClass (finiteKummerMap left) (finiteKummerMap right)
finiteKummerHomomorphism
    (Torsion.torsionCode first second)
    (Torsion.torsionCode first' second') = refl

finiteKummerInjective : ∀ {left right} →
  finiteKummerMap left ≡ finiteKummerMap right → left ≡ right
finiteKummerInjective
    {Torsion.torsionCode first second}
    {Torsion.torsionCode first' second'} equality =
  Torsion.torsionExtensionality
    (congruence firstSquareClass equality)
    (congruence secondSquareClass equality)
  where
    congruence : ∀ {A B : Set} (function : A → B) {x y} →
      x ≡ y → function x ≡ function y
    congruence function refl = refl

squareClassPreimage : SquareClassPair → Torsion.TwoTorsionCode
squareClassPreimage pair =
  Torsion.torsionCode
    (firstSquareClass pair)
    (secondSquareClass pair)

finiteKummerSurjective : ∀ pair →
  finiteKummerMap (squareClassPreimage pair) ≡ pair
finiteKummerSurjective (squareClassPair first second) = refl

finiteKummerKernelTrivial : ∀ point →
  finiteKummerMap point ≡ zeroSquareClass →
  point ≡ Torsion.pointAtInfinityCode
finiteKummerKernelTrivial point kernelEquality =
  finiteKummerInjective kernelEquality

infinityImage :
  finiteKummerMap Torsion.pointAtInfinityCode
  ≡ squareClassPair Torsion.bit0 Torsion.bit0
infinityImage = refl

zeroPointImage :
  finiteKummerMap Torsion.pointZeroCode
  ≡ squareClassPair Torsion.bit1 Torsion.bit0
zeroPointImage = refl

onePointImage :
  finiteKummerMap Torsion.pointOneCode
  ≡ squareClassPair Torsion.bit0 Torsion.bit1
onePointImage = refl

minusOnePointImage :
  finiteKummerMap Torsion.pointMinusOneCode
  ≡ squareClassPair Torsion.bit1 Torsion.bit1
minusOnePointImage = refl

finiteKummerImage : List SquareClassPair
finiteKummerImage =
  finiteKummerMap Torsion.pointAtInfinityCode
  ∷ finiteKummerMap Torsion.pointZeroCode
  ∷ finiteKummerMap Torsion.pointOneCode
  ∷ finiteKummerMap Torsion.pointMinusOneCode
  ∷ []

record FiniteTwoDescentCertificate : Set where
  field
    homomorphism : ∀ left right →
      finiteKummerMap (Torsion.addTorsion left right)
      ≡ addSquareClass (finiteKummerMap left) (finiteKummerMap right)
    injective : ∀ {left right} →
      finiteKummerMap left ≡ finiteKummerMap right → left ≡ right
    surjective : ∀ pair →
      finiteKummerMap (squareClassPreimage pair) ≡ pair
    trivialKernel : ∀ point →
      finiteKummerMap point ≡ zeroSquareClass →
      point ≡ Torsion.pointAtInfinityCode

canonicalFiniteTwoDescentCertificate : FiniteTwoDescentCertificate
canonicalFiniteTwoDescentCertificate = record
  { homomorphism = finiteKummerHomomorphism
  ; injective = finiteKummerInjective
  ; surjective = finiteKummerSurjective
  ; trivialKernel = finiteKummerKernelTrivial
  }

record GlobalTwoDescentBoundary : Set₁ where
  field
    RationalSquareClass : Set
    kummerMapOnRationalPoints : Set
    localConditionsAtFinitePrimes : Set
    localConditionAtInfinity : Set
    twoSelmerGroup : Set
    mordellWeilModuloTwo : Set
    shaTwoTorsion : Set
    descentExactSequence : Set
