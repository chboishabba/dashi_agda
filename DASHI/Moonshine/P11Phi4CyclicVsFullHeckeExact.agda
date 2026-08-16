module DASHI.Moonshine.P11Phi4CyclicVsFullHeckeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew V. Sutherland,
-- Classical modular-polynomial coefficient dataset, phi_j_4.txt.
-- The dataset page states that Phi_N(X,Y) is a canonical equation for X_0(N),
-- parameterizing pairs of elliptic curves related by a CYCLIC isogeny of
-- degree N.  For composite N=4 the coefficient file is therefore the cyclic
-- X_0(4) correspondence, not by itself the complete index-4 Hecke double
-- coset including the noncyclic multiplication-by-2 kernel.
-- No DOI is asserted for the dataset itself.
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- DASHI CONTRIBUTION
--
-- Independently reduce the actual Phi_4 coefficient dataset modulo 11 at the
-- two p=11 labels used by the existing Phi_2 construction.  The exact
-- specializations are
--
--   Phi_4(0,Y) = Y^3 (Y-1)^3,
--   Phi_4(1,Y) = Y^2 (Y-1)^4                  in F_11[Y].
--
-- Hence the CYCLIC degree-4 correspondence has multiplicity matrix
--
--       C4 = [[3,3],[2,4]],
--
-- whose row degree is 6.  This deliberately differs from the full weight-2
-- Hecke T_4 forced by Aristotle's recurrence:
--
--       T4_forced = T2^2 - 2 I = [[4,3],[2,5]].
--
-- The discrepancy is exactly one identity correspondence:
--
--       T4_forced = C4 + I.
--
-- Thus the first independent composite-degree modular-polynomial check does
-- NOT falsify the Hecke recurrence.  Instead it exposes the semantic
-- distinction between the cyclic X_0(4) correspondence and the full Hecke
-- operator.  Geometrically the extra self-correspondence is expected to be the
-- noncyclic degree-4 multiplication-by-2 isogeny with kernel E[2]; that kernel
-- interpretation is recorded as source context, not constructed internally.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

import DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore as Classical
import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11
import DASHI.Moonshine.P11ClassicalTwoIsogenySpectralExact as Spectral
import DASHI.Moonshine.P11AristotleHeckeSquareCrossPollinationExact as Square

------------------------------------------------------------------------
-- Reduced Phi_4 specializations.  Coefficients are c0,...,c6.
------------------------------------------------------------------------

record SexticMod11 : Set where
  constructor sextic11
  field
    c0 c1 c2 c3 c4 c5 c6 : Nat

open SexticMod11 public

phi4AtJ0Mod11 : SexticMod11
phi4AtJ0Mod11 = sextic11 0 0 0 10 3 8 1

phi4AtJ1Mod11 : SexticMod11
phi4AtJ1Mod11 = sextic11 0 0 1 7 6 7 1

yCubedTimesYMinusOneCubed : SexticMod11
yCubedTimesYMinusOneCubed = sextic11 0 0 0 10 3 8 1

ySquaredTimesYMinusOneFourth : SexticMod11
ySquaredTimesYMinusOneFourth = sextic11 0 0 1 7 6 7 1

phi4J0FactorizationExact :
  phi4AtJ0Mod11 ≡ yCubedTimesYMinusOneCubed
phi4J0FactorizationExact = refl

phi4J1FactorizationExact :
  phi4AtJ1Mod11 ≡ ySquaredTimesYMinusOneFourth
phi4J1FactorizationExact = refl

------------------------------------------------------------------------
-- Composite cyclic correspondence needs six neighbours, not ell+1=5.
-- Keep it local rather than misusing ClassicalPrimeDegreeCorrespondence,
-- whose fibre shape is intentionally prime-degree.
------------------------------------------------------------------------

cyclicFourNeighbour : P11.J11Class → Fin 6 → P11.J11Class
cyclicFourNeighbour P11.j0 zero = P11.j0
cyclicFourNeighbour P11.j0 (suc zero) = P11.j0
cyclicFourNeighbour P11.j0 (suc (suc zero)) = P11.j0
cyclicFourNeighbour P11.j0 (suc (suc (suc zero))) = P11.j1
cyclicFourNeighbour P11.j0 (suc (suc (suc (suc zero)))) = P11.j1
cyclicFourNeighbour P11.j0 (suc (suc (suc (suc (suc zero))))) = P11.j1
cyclicFourNeighbour P11.j1 zero = P11.j0
cyclicFourNeighbour P11.j1 (suc zero) = P11.j0
cyclicFourNeighbour P11.j1 (suc (suc zero)) = P11.j1
cyclicFourNeighbour P11.j1 (suc (suc (suc zero))) = P11.j1
cyclicFourNeighbour P11.j1 (suc (suc (suc (suc zero)))) = P11.j1
cyclicFourNeighbour P11.j1 (suc (suc (suc (suc (suc zero))))) = P11.j1

cyclicFourOperator :
  (P11.J11Class → Nat) → P11.J11Class → Nat
cyclicFourOperator observable state =
  Classical.foldFin _+_ 0
    (λ edge → observable (cyclicFourNeighbour state edge))

cyclicFourMultiplicity : P11.J11Class → P11.J11Class → Nat
cyclicFourMultiplicity P11.j0 P11.j0 = 3
cyclicFourMultiplicity P11.j0 P11.j1 = 3
cyclicFourMultiplicity P11.j1 P11.j0 = 2
cyclicFourMultiplicity P11.j1 P11.j1 = 4

cyclicFourRowDegree : P11.J11Class → Nat
cyclicFourRowDegree state =
  cyclicFourMultiplicity state P11.j0
  + cyclicFourMultiplicity state P11.j1

cyclicFourJ0DegreeIsSix : cyclicFourRowDegree P11.j0 ≡ 6
cyclicFourJ0DegreeIsSix = refl

cyclicFourJ1DegreeIsSix : cyclicFourRowDegree P11.j1 ≡ 6
cyclicFourJ1DegreeIsSix = refl

cyclicFourOperatorJ0J0 :
  cyclicFourOperator P11.indicatorJ0 P11.j0 ≡ 3
cyclicFourOperatorJ0J0 = refl

cyclicFourOperatorJ0J1 :
  cyclicFourOperator P11.indicatorJ1 P11.j0 ≡ 3
cyclicFourOperatorJ0J1 = refl

cyclicFourOperatorJ1J0 :
  cyclicFourOperator P11.indicatorJ0 P11.j1 ≡ 2
cyclicFourOperatorJ1J0 = refl

cyclicFourOperatorJ1J1 :
  cyclicFourOperator P11.indicatorJ1 P11.j1 ≡ 4
cyclicFourOperatorJ1J1 = refl

------------------------------------------------------------------------
-- Signed matrix action C4 = [[3,3],[2,4]].
------------------------------------------------------------------------

cyclicFourMatrixAction : P11.IntPair → P11.IntPair
cyclicFourMatrixAction vector =
  P11.intPair
    (((+ 3) *ℤ P11.left vector) +ℤ ((+ 3) *ℤ P11.right vector))
    (((+ 2) *ℤ P11.left vector) +ℤ ((+ 4) *ℤ P11.right vector))

cyclicFourConstantModeIsSix :
  cyclicFourMatrixAction P11.constantEigenvector
  ≡ P11.scalePair (+ 6) P11.constantEigenvector
cyclicFourConstantModeIsSix = refl

cyclicFourNonconstantModeIsOne :
  cyclicFourMatrixAction P11.nonconstantEigenvector
  ≡ P11.scalePair (+ 1) P11.nonconstantEigenvector
cyclicFourNonconstantModeIsOne = refl

------------------------------------------------------------------------
-- Exact correction: C4 + I is the full T4 forced by the Hecke recurrence.
------------------------------------------------------------------------

cyclicPlusIdentity : P11.IntPair → P11.IntPair
cyclicPlusIdentity vector =
  Square.addPair (cyclicFourMatrixAction vector) vector

cyclicPlusIdentityOnJ0Basis :
  cyclicPlusIdentity Spectral.basisJ0
  ≡ P11.intPair (+ 4) (+ 2)
cyclicPlusIdentityOnJ0Basis = refl

cyclicPlusIdentityOnJ1Basis :
  cyclicPlusIdentity Spectral.basisJ1
  ≡ P11.intPair (+ 3) (+ 5)
cyclicPlusIdentityOnJ1Basis = refl

cyclicPlusIdentityMatchesForcedT4OnJ0 :
  cyclicPlusIdentity Spectral.basisJ0
  ≡ Square.forcedT4Action Spectral.basisJ0
cyclicPlusIdentityMatchesForcedT4OnJ0 = refl

cyclicPlusIdentityMatchesForcedT4OnJ1 :
  cyclicPlusIdentity Spectral.basisJ1
  ≡ Square.forcedT4Action Spectral.basisJ1
cyclicPlusIdentityMatchesForcedT4OnJ1 = refl

cyclicPlusIdentityConstantModeIsSeven :
  cyclicPlusIdentity P11.constantEigenvector
  ≡ P11.scalePair (+ 7) P11.constantEigenvector
cyclicPlusIdentityConstantModeIsSeven = refl

cyclicPlusIdentityNonconstantModeIsTwo :
  cyclicPlusIdentity P11.nonconstantEigenvector
  ≡ P11.scalePair (+ 2) P11.nonconstantEigenvector
cyclicPlusIdentityNonconstantModeIsTwo = refl

cyclicPlusIdentityMatchesAristotleConstantSquare :
  cyclicPlusIdentity P11.constantEigenvector
  ≡ P11.scalePair (Square.constantModeLane 2) P11.constantEigenvector
cyclicPlusIdentityMatchesAristotleConstantSquare = refl

cyclicPlusIdentityMatchesAristotleNonconstantSquare :
  cyclicPlusIdentity P11.nonconstantEigenvector
  ≡ P11.scalePair (Square.nonconstantModeLane 2) P11.nonconstantEigenvector
cyclicPlusIdentityMatchesAristotleNonconstantSquare = refl

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record P11Phi4CyclicVsFullHeckeBoundary : Set where
  field
    actualPhi4SpecializationsReducedMod11 : Bool
    actualPhi4SpecializationsReducedMod11IsTrue :
      actualPhi4SpecializationsReducedMod11 ≡ true

    cyclicDegreeFourMatrixConstructed : Bool
    cyclicDegreeFourMatrixConstructedIsTrue :
      cyclicDegreeFourMatrixConstructed ≡ true

    cyclicPartPlusIdentityMatchesForcedFullT4 : Bool
    cyclicPartPlusIdentityMatchesForcedFullT4IsTrue :
      cyclicPartPlusIdentityMatchesForcedFullT4 ≡ true

    geometricE2KernelSelfIsogenyConstructedHere : Bool
    geometricE2KernelSelfIsogenyConstructedHereIsFalse :
      geometricE2KernelSelfIsogenyConstructedHere ≡ false

canonicalP11Phi4CyclicVsFullHeckeBoundary :
  P11Phi4CyclicVsFullHeckeBoundary
canonicalP11Phi4CyclicVsFullHeckeBoundary =
  record
    { actualPhi4SpecializationsReducedMod11 = true
    ; actualPhi4SpecializationsReducedMod11IsTrue = refl
    ; cyclicDegreeFourMatrixConstructed = true
    ; cyclicDegreeFourMatrixConstructedIsTrue = refl
    ; cyclicPartPlusIdentityMatchesForcedFullT4 = true
    ; cyclicPartPlusIdentityMatchesForcedFullT4IsTrue = refl
    ; geometricE2KernelSelfIsogenyConstructedHere = false
    ; geometricE2KernelSelfIsogenyConstructedHereIsFalse = refl
    }
