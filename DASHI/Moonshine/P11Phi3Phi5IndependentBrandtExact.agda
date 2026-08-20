module DASHI.Moonshine.P11Phi3Phi5IndependentBrandtExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew V. Sutherland,
-- Classical modular-polynomial coefficient datasets phi_j_3.txt and
-- phi_j_5.txt, published with the MIT Classical Modular Polynomials tables.
-- The dataset page states that Phi_N(X,Y) is a canonical equation for X_0(N),
-- parameterizing cyclic degree-N isogenies.  No DOI is asserted for the data
-- files themselves.
--
-- Reinier Bröker, Kristin Lauter and Andrew V. Sutherland,
-- "Modular polynomials via isogeny volcanoes",
-- Mathematics of Computation 81 (2012), 1201--1231.
-- DOI: 10.1090/S0025-5718-2011-02508-1.
--
-- DASHI CONTRIBUTION
--
-- Independently reduce the published Phi_3 and Phi_5 coefficient datasets at
-- the two actual characteristic-11 supersingular j-residues 0 and 1.
-- The exact factorizations in F_11[Y] are
--
--   Phi_3(0,Y) = Y (Y-1)^3,
--   Phi_3(1,Y) = Y^2 (Y-1)^2,
--
--   Phi_5(0,Y) = Y^3 (Y-1)^3,
--   Phi_5(1,Y) = Y^2 (Y-1)^4.
--
-- Therefore their multiplicity matrices are exactly
--
--   [[1,3],[2,2]] = B_11(3),
--   [[3,3],[2,4]] = B_11(5),
--
-- independently confirming the Brandt matrices previously forced from the
-- level-11 newform eigenvalues plus automorphism weighting.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact as Brandt

------------------------------------------------------------------------
-- Reduced polynomial coefficient carriers.
------------------------------------------------------------------------

record QuarticMod11 : Set where
  constructor quartic11
  field
    q0 q1 q2 q3 q4 : Nat

open QuarticMod11 public

record SexticMod11 : Set where
  constructor sextic11
  field
    s0 s1 s2 s3 s4 s5 s6 : Nat

open SexticMod11 public

------------------------------------------------------------------------
-- Phi_3 specializations.
--
-- Y(Y-1)^3 = -Y + 3Y^2 - 3Y^3 + Y^4
--            = 10Y + 3Y^2 + 8Y^3 + Y^4 mod 11.
-- Y^2(Y-1)^2 = Y^2 - 2Y^3 + Y^4
--             = Y^2 + 9Y^3 + Y^4 mod 11.
------------------------------------------------------------------------

phi3AtJ0Mod11 : QuarticMod11
phi3AtJ0Mod11 = quartic11 0 10 3 8 1

phi3AtJ1Mod11 : QuarticMod11
phi3AtJ1Mod11 = quartic11 0 0 1 9 1

phi3FactorJ0 : QuarticMod11
phi3FactorJ0 = quartic11 0 10 3 8 1

phi3FactorJ1 : QuarticMod11
phi3FactorJ1 = quartic11 0 0 1 9 1

phi3J0FactorizationExact : phi3AtJ0Mod11 ≡ phi3FactorJ0
phi3J0FactorizationExact = refl

phi3J1FactorizationExact : phi3AtJ1Mod11 ≡ phi3FactorJ1
phi3J1FactorizationExact = refl

------------------------------------------------------------------------
-- Phi_5 specializations.
--
-- Y^3(Y-1)^3 = -Y^3 + 3Y^4 - 3Y^5 + Y^6
--              = 10Y^3 + 3Y^4 + 8Y^5 + Y^6 mod 11.
-- Y^2(Y-1)^4 = Y^2 - 4Y^3 + 6Y^4 - 4Y^5 + Y^6
--              = Y^2 + 7Y^3 + 6Y^4 + 7Y^5 + Y^6 mod 11.
------------------------------------------------------------------------

phi5AtJ0Mod11 : SexticMod11
phi5AtJ0Mod11 = sextic11 0 0 0 10 3 8 1

phi5AtJ1Mod11 : SexticMod11
phi5AtJ1Mod11 = sextic11 0 0 1 7 6 7 1

phi5FactorJ0 : SexticMod11
phi5FactorJ0 = sextic11 0 0 0 10 3 8 1

phi5FactorJ1 : SexticMod11
phi5FactorJ1 = sextic11 0 0 1 7 6 7 1

phi5J0FactorizationExact : phi5AtJ0Mod11 ≡ phi5FactorJ0
phi5J0FactorizationExact = refl

phi5J1FactorizationExact : phi5AtJ1Mod11 ≡ phi5FactorJ1
phi5J1FactorizationExact = refl

------------------------------------------------------------------------
-- Independent multiplicity matrices and exact comparison with Brandt output.
------------------------------------------------------------------------

phi3MultiplicityMatrix : Brandt.P11BrandtMatrix
phi3MultiplicityMatrix = Brandt.brandtMatrix 1 3 2 2

phi5MultiplicityMatrix : Brandt.P11BrandtMatrix
phi5MultiplicityMatrix = Brandt.brandtMatrix 3 3 2 4

phi3IndependentCheckMatchesB11_3 :
  phi3MultiplicityMatrix ≡ Brandt.B11_3
phi3IndependentCheckMatchesB11_3 = refl

phi5IndependentCheckMatchesB11_5 :
  phi5MultiplicityMatrix ≡ Brandt.B11_5
phi5IndependentCheckMatchesB11_5 = refl

phi3RowDegreesAreFour :
  Brandt.row0Degree phi3MultiplicityMatrix ≡ 4
  × Brandt.row1Degree phi3MultiplicityMatrix ≡ 4
phi3RowDegreesAreFour = refl , refl

phi5RowDegreesAreSix :
  Brandt.row0Degree phi5MultiplicityMatrix ≡ 6
  × Brandt.row1Degree phi5MultiplicityMatrix ≡ 6
phi5RowDegreesAreSix = refl , refl

record P11Phi3Phi5IndependentBoundary : Set where
  field
    phi3IndependentMod11ReductionConstructed : Bool
    phi3IndependentMod11ReductionConstructedIsTrue :
      phi3IndependentMod11ReductionConstructed ≡ true

    phi5IndependentMod11ReductionConstructed : Bool
    phi5IndependentMod11ReductionConstructedIsTrue :
      phi5IndependentMod11ReductionConstructed ≡ true

    phi3MatchesSourceForcedBrandtMatrix : Bool
    phi3MatchesSourceForcedBrandtMatrixIsTrue :
      phi3MatchesSourceForcedBrandtMatrix ≡ true

    phi5MatchesSourceForcedBrandtMatrix : Bool
    phi5MatchesSourceForcedBrandtMatrixIsTrue :
      phi5MatchesSourceForcedBrandtMatrix ≡ true

canonicalP11Phi3Phi5IndependentBoundary : P11Phi3Phi5IndependentBoundary
canonicalP11Phi3Phi5IndependentBoundary =
  record
    { phi3IndependentMod11ReductionConstructed = true
    ; phi3IndependentMod11ReductionConstructedIsTrue = refl
    ; phi5IndependentMod11ReductionConstructed = true
    ; phi5IndependentMod11ReductionConstructedIsTrue = refl
    ; phi3MatchesSourceForcedBrandtMatrix = true
    ; phi3MatchesSourceForcedBrandtMatrixIsTrue = refl
    ; phi5MatchesSourceForcedBrandtMatrix = true
    ; phi5MatchesSourceForcedBrandtMatrixIsTrue = refl
    }
