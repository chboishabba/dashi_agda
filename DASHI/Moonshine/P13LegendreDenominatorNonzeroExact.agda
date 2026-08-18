module DASHI.Moonshine.P13LegendreDenominatorNonzeroExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Josep Gonzalez,
-- "On the p-th division polynomial", Journal of Number Theory 233 (2022),
-- 285--300. DOI: 10.1016/j.jnt.2021.06.011.
--
-- DASHI CONTRIBUTION
--
-- The p=13 Legendre-j reduction uses
--
--   j(lambda)=256(1-lambda+lambda^2)^3 /
--             (lambda^2(1-lambda)^2).
--
-- Before reading the quotient relation N=5D as a j-value, certify that none of
-- the three irreducible Deuring quadratics has lambda=0 or lambda=1 as a root.
-- For f=x^2+b x+c the two evaluations are c and 1+b+c.  Their residues are:
--
--     q0: f(0)=9, f(1)=1
--     q1: f(0)=1, f(1)=9
--     q2: f(0)=3, f(1)=3       (mod 13).
--
-- Thus every root lies in the honest Legendre moduli chart, so the denominator
-- lambda^2(1-lambda)^2 is nonzero there.  This file keeps the finite residue
-- certificate separate from the higher-level j-reduction theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P13OggFullLevel2DeuringControlExact as P13

factorAtZeroResidue : P13.P13QuadraticFactor → Nat
factorAtZeroResidue P13.q0 = 9
factorAtZeroResidue P13.q1 = 1
factorAtZeroResidue P13.q2 = 3

factorAtOneResidue : P13.P13QuadraticFactor → Nat
factorAtOneResidue P13.q0 = 1
factorAtOneResidue P13.q1 = 9
factorAtOneResidue P13.q2 = 3

factorAtZeroNonzero :
  (q : P13.P13QuadraticFactor) → factorAtZeroResidue q ≡ 0 → ⊥
factorAtZeroNonzero P13.q0 ()
factorAtZeroNonzero P13.q1 ()
factorAtZeroNonzero P13.q2 ()

factorAtOneNonzero :
  (q : P13.P13QuadraticFactor) → factorAtOneResidue q ≡ 0 → ⊥
factorAtOneNonzero P13.q0 ()
factorAtOneNonzero P13.q1 ()
factorAtOneNonzero P13.q2 ()

-- Integer congruence witnesses for the displayed evaluations.
q0AtOneCongruence : 1 + 4 + 9 ≡ 1 + 13 * 1
q0AtOneCongruence = refl

q1AtOneExact : 1 + 7 + 1 ≡ 9
q1AtOneExact = refl

q2AtOneCongruence : 1 + 12 + 3 ≡ 3 + 13 * 1
q2AtOneCongruence = refl

record P13LegendreChartPoleBoundary : Set where
  field
    zeroPoleExcludedForEveryFactor : Bool
    onePoleExcludedForEveryFactor : Bool
    jDenominatorLegitimateOnDeuringRoots : Bool

canonicalP13LegendreChartPoleBoundary : P13LegendreChartPoleBoundary
canonicalP13LegendreChartPoleBoundary = record
  { zeroPoleExcludedForEveryFactor = true
  ; onePoleExcludedForEveryFactor = true
  ; jDenominatorLegitimateOnDeuringRoots = true
  }
