module DASHI.Moonshine.P5LegendreJZeroF25ResidueExact where

------------------------------------------------------------------------
-- FINITE F_25 RESIDUE CHART FOR THE p=5, j=0 EXCEPTIONAL LEGENDRE BRANCH
--
-- PRIMARY SOURCES / CROSS-POLLINATION
--
-- Rudolf Lidl and Harald Niederreiter,
-- "Finite Fields", Encyclopedia of Mathematics and its Applications 20,
-- Cambridge University Press, 2nd ed., 1997.
-- DOI: 10.1017/CBO9780511525926.
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", 2nd ed., GTM 106, Springer, 2009.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- The implementation pattern deliberately mirrors the earlier F9 quadratic
-- extension tranche (#572), but does NOT reuse its ternary carrier.
--
-- For p=5 the j=0 Legendre factor
--
--   q(lambda)=lambda^2-lambda+1
--
-- is irreducible over F_5.  Work in the concrete quotient chart
--
--   F_25 = F_5[alpha]/(alpha^2-alpha+1),
--
-- represented by residue pairs a+b alpha.  Since alpha^2=alpha-1,
--
--   (a+b alpha)(c+d alpha)
--     = (ac-bd) + (ad+bc+bd) alpha.
--
-- DASHI CONTRIBUTION
--
-- Construct exactly the finite residue arithmetic needed by the Dwork/Legendre
-- local-unit cutset.  For both roots alpha and 1-alpha we prove:
--
--   q(root)=0,
--   2 root - 1 != 0,                 [simple branch]
--   root^2 (1-root)^2 != 0.          [Legendre denominator]
--
-- This is finite residue geometry ONLY.  No Q_5, Witt/Teichmuller lift, or
-- p-adic depth-one parameter is constructed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_%_)

record F25Residue : Set where
  constructor f25
  field
    constant alphaCoefficient : Nat

open F25Residue public

normalize5 : Nat → Nat
normalize5 n = n % 5

f25Zero : F25Residue
f25Zero = f25 0 0

f25One : F25Residue
f25One = f25 1 0

f25Alpha : F25Residue
f25Alpha = f25 0 1

f5Sub : Nat → Nat → Nat
f5Sub x y = (normalize5 x + 5 - normalize5 y) % 5

f25Add : F25Residue → F25Residue → F25Residue
f25Add (f25 a b) (f25 c d) =
  f25 ((a + c) % 5) ((b + d) % 5)

f25Sub : F25Residue → F25Residue → F25Residue
f25Sub (f25 a b) (f25 c d) =
  f25 (f5Sub a c) (f5Sub b d)

f25Mul : F25Residue → F25Residue → F25Residue
f25Mul (f25 a b) (f25 c d) =
  f25
    (f5Sub (a * c) (b * d))
    ((a * d + b * c + b * d) % 5)

f25Square : F25Residue → F25Residue
f25Square x = f25Mul x x

f25Two : F25Residue
f25Two = f25 2 0

jZeroQuadratic : F25Residue → F25Residue
jZeroQuadratic x = f25Add (f25Sub (f25Square x) x) f25One

jZeroDerivative : F25Residue → F25Residue
jZeroDerivative x = f25Sub (f25Mul f25Two x) f25One

legendreDenominator : F25Residue → F25Residue
legendreDenominator x =
  f25Mul (f25Square x) (f25Square (f25Sub f25One x))

f25ConjugateRoot : F25Residue
f25ConjugateRoot = f25Sub f25One f25Alpha

------------------------------------------------------------------------
-- Exact quotient arithmetic.
------------------------------------------------------------------------

alphaSquare : f25Square f25Alpha ≡ f25 4 1
alphaSquare = refl

alphaIsJZeroRoot : jZeroQuadratic f25Alpha ≡ f25Zero
alphaIsJZeroRoot = refl

alphaDerivative : jZeroDerivative f25Alpha ≡ f25 4 2
alphaDerivative = refl

alphaDenominator : legendreDenominator f25Alpha ≡ f25One
alphaDenominator = refl

conjugateRootValue : f25ConjugateRoot ≡ f25 1 4
conjugateRootValue = refl

conjugateIsJZeroRoot : jZeroQuadratic f25ConjugateRoot ≡ f25Zero
conjugateIsJZeroRoot = refl

conjugateDerivative : jZeroDerivative f25ConjugateRoot ≡ f25 1 3
conjugateDerivative = refl

conjugateDenominator : legendreDenominator f25ConjugateRoot ≡ f25One
conjugateDenominator = refl

------------------------------------------------------------------------
-- Constructor-level nonzero certificates.
------------------------------------------------------------------------

alphaDerivativeNonzero : jZeroDerivative f25Alpha ≡ f25Zero → ⊥
alphaDerivativeNonzero ()

alphaDenominatorNonzero : legendreDenominator f25Alpha ≡ f25Zero → ⊥
alphaDenominatorNonzero ()

conjugateDerivativeNonzero :
  jZeroDerivative f25ConjugateRoot ≡ f25Zero → ⊥
conjugateDerivativeNonzero ()

conjugateDenominatorNonzero :
  legendreDenominator f25ConjugateRoot ≡ f25Zero → ⊥
conjugateDenominatorNonzero ()

record P5LegendreJZeroF25ResidueBoundary : Set where
  field
    quadraticExtensionChartConstructed : Bool
    bothJZeroRootsConstructed : Bool
    bothRootsSimpleByDerivativeNonzero : Bool
    bothLegendreDenominatorsNonzero : Bool
    finiteResidueUnitInputsComplete : Bool
    F25PromotedToQ5 : Bool
    TeichmullerLiftConstructed : Bool
    localParameterDepthOneConstructed : Bool

canonicalP5LegendreJZeroF25ResidueBoundary :
  P5LegendreJZeroF25ResidueBoundary
canonicalP5LegendreJZeroF25ResidueBoundary = record
  { quadraticExtensionChartConstructed = true
  ; bothJZeroRootsConstructed = true
  ; bothRootsSimpleByDerivativeNonzero = true
  ; bothLegendreDenominatorsNonzero = true
  ; finiteResidueUnitInputsComplete = true
  ; F25PromotedToQ5 = false
  ; TeichmullerLiftConstructed = false
  ; localParameterDepthOneConstructed = false
  }
