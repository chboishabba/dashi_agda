module DASHI.Moonshine.P7P11LegendreJ1728ResidueCertificatesExact where

------------------------------------------------------------------------
-- FINITE RESIDUE CERTIFICATES FOR THE EXCEPTIONAL j=1728 BRANCHES
--
-- PRIMARY CONTEXT
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", 2nd ed., GTM 106, Springer, 2009.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- The exact Legendre identity is
--
--   j(lambda)-1728
--     = 64 (lambda-2)^2 (lambda+1)^2 (2lambda-1)^2
--       / (lambda^2(1-lambda)^2).
--
-- For p=7 and p=11 all three j=1728 Legendre preimages are rational:
--
--   lambda=2, lambda=-1, lambda=1/2.
--
-- DASHI CONTRIBUTION
--
-- Compute the finite residues at those six actual points.  In each case the
-- selected branch factor is zero, while the complementary-factor product and
-- Legendre denominator are nonzero.  These are precisely the finite inputs a
-- future p-adic local-ring adapter can turn into valuation-zero unit witnesses.
--
-- This file does NOT construct Q_p, Teichmuller lifts, or a p-adic parameter.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_%_)

------------------------------------------------------------------------
-- Residue expressions using nonnegative representatives.
------------------------------------------------------------------------

lambdaMinusTwoResidue : Nat → Nat → Nat
lambdaMinusTwoResidue p lambda = (lambda + p - 2) % p

lambdaPlusOneResidue : Nat → Nat → Nat
lambdaPlusOneResidue p lambda = (lambda + 1) % p

twoLambdaMinusOneResidue : Nat → Nat → Nat
twoLambdaMinusOneResidue p lambda = (2 * lambda + p - 1) % p

legendreDenominatorResidue : Nat → Nat → Nat
legendreDenominatorResidue p lambda =
  (lambda * lambda * ((1 + p - lambda) * (1 + p - lambda))) % p

minusTwoComplementResidue : Nat → Nat → Nat
minusTwoComplementResidue p lambda =
  (lambdaPlusOneResidue p lambda * twoLambdaMinusOneResidue p lambda) % p

plusOneComplementResidue : Nat → Nat → Nat
plusOneComplementResidue p lambda =
  (lambdaMinusTwoResidue p lambda * twoLambdaMinusOneResidue p lambda) % p

halfComplementResidue : Nat → Nat → Nat
halfComplementResidue p lambda =
  (lambdaMinusTwoResidue p lambda * lambdaPlusOneResidue p lambda) % p

------------------------------------------------------------------------
-- p=7: lambda = 2, 6=-1, 4=1/2.
------------------------------------------------------------------------

p7Lambda2SelectedZero : lambdaMinusTwoResidue 7 2 ≡ 0
p7Lambda2SelectedZero = refl

p7Lambda2Complement : minusTwoComplementResidue 7 2 ≡ 2
p7Lambda2Complement = refl

p7Lambda2Denominator : legendreDenominatorResidue 7 2 ≡ 4
p7Lambda2Denominator = refl

p7Lambda6SelectedZero : lambdaPlusOneResidue 7 6 ≡ 0
p7Lambda6SelectedZero = refl

p7Lambda6Complement : plusOneComplementResidue 7 6 ≡ 2
p7Lambda6Complement = refl

p7Lambda6Denominator : legendreDenominatorResidue 7 6 ≡ 4
p7Lambda6Denominator = refl

p7Lambda4SelectedZero : twoLambdaMinusOneResidue 7 4 ≡ 0
p7Lambda4SelectedZero = refl

p7Lambda4Complement : halfComplementResidue 7 4 ≡ 3
p7Lambda4Complement = refl

p7Lambda4Denominator : legendreDenominatorResidue 7 4 ≡ 4
p7Lambda4Denominator = refl

------------------------------------------------------------------------
-- p=11: lambda = 2, 10=-1, 6=1/2.
------------------------------------------------------------------------

p11Lambda2SelectedZero : lambdaMinusTwoResidue 11 2 ≡ 0
p11Lambda2SelectedZero = refl

p11Lambda2Complement : minusTwoComplementResidue 11 2 ≡ 9
p11Lambda2Complement = refl

p11Lambda2Denominator : legendreDenominatorResidue 11 2 ≡ 4
p11Lambda2Denominator = refl

p11Lambda10SelectedZero : lambdaPlusOneResidue 11 10 ≡ 0
p11Lambda10SelectedZero = refl

p11Lambda10Complement : plusOneComplementResidue 11 10 ≡ 9
p11Lambda10Complement = refl

p11Lambda10Denominator : legendreDenominatorResidue 11 10 ≡ 4
p11Lambda10Denominator = refl

p11Lambda6SelectedZero : twoLambdaMinusOneResidue 11 6 ≡ 0
p11Lambda6SelectedZero = refl

p11Lambda6Complement : halfComplementResidue 11 6 ≡ 6
p11Lambda6Complement = refl

p11Lambda6Denominator : legendreDenominatorResidue 11 6 ≡ 9
p11Lambda6Denominator = refl

------------------------------------------------------------------------
-- Constructor-level nonzero witnesses for the exact displayed residues.
------------------------------------------------------------------------

p7ComplementTwoNonzero : 2 ≡ 0 → ⊥
p7ComplementTwoNonzero ()

p7ComplementThreeNonzero : 3 ≡ 0 → ⊥
p7ComplementThreeNonzero ()

p7DenominatorFourNonzero : 4 ≡ 0 → ⊥
p7DenominatorFourNonzero ()

p11ComplementNineNonzero : 9 ≡ 0 → ⊥
p11ComplementNineNonzero ()

p11ComplementSixNonzero : 6 ≡ 0 → ⊥
p11ComplementSixNonzero ()

p11DenominatorFourNonzero : 4 ≡ 0 → ⊥
p11DenominatorFourNonzero ()

p11DenominatorNineNonzero : 9 ≡ 0 → ⊥
p11DenominatorNineNonzero ()

record P7P11LegendreJ1728ResidueCertificatesBoundary : Set where
  field
    allSixSelectedFactorsCertifiedZero : Bool
    allSixComplementProductsCertifiedNonzero : Bool
    allSixDenominatorsCertifiedNonzero : Bool
    residueUnitInputsAvailableForP7P11 : Bool
    padicLiftConstructedHere : Bool
    branchDepthOneConstructedHere : Bool

canonicalP7P11LegendreJ1728ResidueCertificatesBoundary :
  P7P11LegendreJ1728ResidueCertificatesBoundary
canonicalP7P11LegendreJ1728ResidueCertificatesBoundary = record
  { allSixSelectedFactorsCertifiedZero = true
  ; allSixComplementProductsCertifiedNonzero = true
  ; allSixDenominatorsCertifiedNonzero = true
  ; residueUnitInputsAvailableForP7P11 = true
  ; padicLiftConstructedHere = false
  ; branchDepthOneConstructedHere = false
  }
