module DASHI.Moonshine.LegendreExceptionalCertifiedResiduePointsExact where

------------------------------------------------------------------------
-- EXPLICIT CERTIFIED RESIDUE POINTS FOR THE HENSEL/DWORK LOCAL SOURCE
--
-- PRIMARY SOURCES
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", 2nd ed., GTM 106, Springer, 2009.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- Bernard Dwork, "$p$-adic cycles", Publ. Math. IHES 37 (1969), 27--115.
-- DOI: 10.1007/BF02684886.
--
-- DASHI CONTRIBUTION
--
-- Connect the generic Hensel source to the already-constructed finite residue
-- geometry instead of leaving its `finitePoint` anonymous.
--
-- * p=5, j=0 uses the concrete F_25 root alpha of lambda^2-lambda+1;
-- * p=7, j=1728 uses the rational branch lambda=2;
-- * p=11, j=1728 uses the rational branch lambda=2.
--
-- The derivative/outer residues below are the actual simple-factor / Legendre
-- rational-function unit residues for those chosen branches.  This file still
-- does not identify a finite residue carrier with its p-adic lift; that step is
-- exactly the Hensel operation in LegendreExceptionalPadicHenselConstructionExact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.LegendreExceptionalPadicLiftSameObjectExact as Lift
import DASHI.Moonshine.P5LegendreJZeroF25ResidueExact as P5
import DASHI.Moonshine.P7P11LegendreJ1728ResidueCertificatesExact as P7P11

------------------------------------------------------------------------
-- p=5, j=0, centre alpha in F_25.
-- q'(alpha)=4+2 alpha is nonzero and the outer j-factor residue is one because
-- 256 == 1 (mod 5) and the displayed Legendre denominator is one.
------------------------------------------------------------------------

p5OuterOneNonzero : P5.f25One ≡ P5.f25Zero → ⊥
p5OuterOneNonzero ()

p5JZeroAlphaFinitePoint : Lift.ExceptionalFiniteResiduePoint P5.F25Residue
p5JZeroAlphaFinitePoint = record
  { Lift.zero = P5.f25Zero
  ; Lift.centre = P5.f25Alpha
  ; Lift.derivativeResidue = P5.jZeroDerivative P5.f25Alpha
  ; Lift.outerUnitResidue = P5.f25One
  ; Lift.derivativeResidueNonzero = P5.alphaDerivativeNonzero
  ; Lift.outerUnitResidueNonzero = p5OuterOneNonzero
  }

p5CentreIsCertifiedJZeroRoot :
  P5.jZeroQuadratic (Lift.centre p5JZeroAlphaFinitePoint) ≡ P5.f25Zero
p5CentreIsCertifiedJZeroRoot = P5.alphaIsJZeroRoot

------------------------------------------------------------------------
-- p=7, j=1728, selected linear branch lambda-2 at lambda=2.
-- Its simple derivative is 1.  For the outer square factor,
-- 64*(lambda+1)^2*(2lambda-1)^2 / D reduces to 1 at lambda=2 mod 7.
------------------------------------------------------------------------

p7OneNonzero : 1 ≡ 0 → ⊥
p7OneNonzero ()

p7J1728Lambda2FinitePoint : Lift.ExceptionalFiniteResiduePoint Nat
p7J1728Lambda2FinitePoint = record
  { Lift.zero = 0
  ; Lift.centre = 2
  ; Lift.derivativeResidue = 1
  ; Lift.outerUnitResidue = 1
  ; Lift.derivativeResidueNonzero = p7OneNonzero
  ; Lift.outerUnitResidueNonzero = p7OneNonzero
  }

p7CentreSelectedFactorZero :
  P7P11.lambdaMinusTwoResidue 7 (Lift.centre p7J1728Lambda2FinitePoint) ≡ 0
p7CentreSelectedFactorZero = P7P11.p7Lambda2SelectedZero

p7CentreComplementCertified :
  P7P11.minusTwoComplementResidue 7 (Lift.centre p7J1728Lambda2FinitePoint) ≡ 2
p7CentreComplementCertified = P7P11.p7Lambda2Complement

p7CentreDenominatorCertified :
  P7P11.legendreDenominatorResidue 7 (Lift.centre p7J1728Lambda2FinitePoint) ≡ 4
p7CentreDenominatorCertified = P7P11.p7Lambda2Denominator

------------------------------------------------------------------------
-- p=11, same branch lambda-2 at lambda=2.
-- The exact outer residue is 9:
--   64 == 9,
--   ((lambda+1)(2lambda-1))^2 == 9^2 == 4,
--   denominator == 4,
-- hence outer == 9 mod 11.
------------------------------------------------------------------------

p11OneNonzero : 1 ≡ 0 → ⊥
p11OneNonzero ()

p11NineNonzero : 9 ≡ 0 → ⊥
p11NineNonzero ()

p11J1728Lambda2FinitePoint : Lift.ExceptionalFiniteResiduePoint Nat
p11J1728Lambda2FinitePoint = record
  { Lift.zero = 0
  ; Lift.centre = 2
  ; Lift.derivativeResidue = 1
  ; Lift.outerUnitResidue = 9
  ; Lift.derivativeResidueNonzero = p11OneNonzero
  ; Lift.outerUnitResidueNonzero = p11NineNonzero
  }

p11CentreSelectedFactorZero :
  P7P11.lambdaMinusTwoResidue 11 (Lift.centre p11J1728Lambda2FinitePoint) ≡ 0
p11CentreSelectedFactorZero = P7P11.p11Lambda2SelectedZero

p11CentreComplementCertified :
  P7P11.minusTwoComplementResidue 11 (Lift.centre p11J1728Lambda2FinitePoint) ≡ 9
p11CentreComplementCertified = P7P11.p11Lambda2Complement

p11CentreDenominatorCertified :
  P7P11.legendreDenominatorResidue 11 (Lift.centre p11J1728Lambda2FinitePoint) ≡ 4
p11CentreDenominatorCertified = P7P11.p11Lambda2Denominator

record LegendreExceptionalCertifiedResiduePointsBoundary : Set where
  field
    p5JZeroPointAdapted : Bool
    p7J1728PointAdapted : Bool
    p11J1728PointAdapted : Bool
    finiteRootCertificatesReused : Bool
    derivativeUnitResiduesExplicit : Bool
    outerUnitResiduesExplicit : Bool
    finiteResiduesPromotedToPadicIdentity : Bool

canonicalLegendreExceptionalCertifiedResiduePointsBoundary :
  LegendreExceptionalCertifiedResiduePointsBoundary
canonicalLegendreExceptionalCertifiedResiduePointsBoundary = record
  { p5JZeroPointAdapted = true
  ; p7J1728PointAdapted = true
  ; p11J1728PointAdapted = true
  ; finiteRootCertificatesReused = true
  ; derivativeUnitResiduesExplicit = true
  ; outerUnitResiduesExplicit = true
  ; finiteResiduesPromotedToPadicIdentity = false
  }
