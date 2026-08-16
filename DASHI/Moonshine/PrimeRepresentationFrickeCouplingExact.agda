module DASHI.Moonshine.PrimeRepresentationFrickeCouplingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Springer, 1991.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7, pp. 1-8.
-- MR 417184; no DOI assigned.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230-239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Couple the independently constructed SO(3) restriction lane to the finite
-- prime-level Fricke genus control without using the external Ogg label.
--
-- For p=2j+1, the elliptic-point counts entering the prime-level X0(p) genus
-- formula are read directly from the SO(3) characters at the order-two and
-- order-three rotations:
--
--   e2(j) = 1 + chi_j(pi),
--   e3(j) = 1 + chi_j(2*pi/3).
--
-- The integer statements are encoded below by exact recurrences, avoiding a
-- coercion from signed character values back into Nat.  They reproduce every
-- e2/e3 entry of the 19-prime Fricke control table, including the p=3 special
-- value e3=1.
--
-- Consequently the representation side reconstructs g(X0(p)) by
--
--   g_rep = (p+1 - 3 e2 - 4 e3)/12.
--
-- The only remaining input in the Fricke quotient Riemann-Hurwitz defect is
-- the arithmetic Fricke fixed-point count
--
--   r_p = h(-4p) + h(-p).
--
-- Define
--
--   D_rep+arith(p) = (2*g_rep + 2) - r_p.
--
-- On every odd prime control below 72 this computes exactly
--
--   D_rep+arith(p) = 4*g(X0+(p)).
--
-- Hence the defect is zero exactly on the finite Ogg locus.  This is the
-- concrete representation/modular coupling requested by the research lane:
-- representation characters supply the elliptic/orbifold part, while class
-- numbers supply the genuinely arithmetic Fricke ramification part.  Neither
-- column alone is promoted to a global Ogg theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_)
open import Data.Nat using (_∸_; _/_)

import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact as Fixed
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke

------------------------------------------------------------------------
-- Elliptic counts from the actual SO(3) character recurrences.
------------------------------------------------------------------------

ellipticOrder2FromJ : Nat → Nat
ellipticOrder2FromJ zero = 2
ellipticOrder2FromJ (suc zero) = 0
ellipticOrder2FromJ (suc (suc j)) = ellipticOrder2FromJ j

ellipticOrder3FromJ : Nat → Nat
ellipticOrder3FromJ zero = 2
ellipticOrder3FromJ (suc zero) = 1
ellipticOrder3FromJ (suc (suc zero)) = 0
ellipticOrder3FromJ (suc (suc (suc j))) = ellipticOrder3FromJ j

ellipticOrder2IsOnePlusHalfTurnCharacter :
  (j : Nat) →
  (+ (ellipticOrder2FromJ j))
  ≡ (+ 1) +ℤ Fixed.halfTurnCharacter j
ellipticOrder2IsOnePlusHalfTurnCharacter zero = refl
ellipticOrder2IsOnePlusHalfTurnCharacter (suc zero) = refl
ellipticOrder2IsOnePlusHalfTurnCharacter (suc (suc j)) =
  ellipticOrder2IsOnePlusHalfTurnCharacter j

ellipticOrder3IsOnePlusThirdTurnCharacter :
  (j : Nat) →
  (+ (ellipticOrder3FromJ j))
  ≡ (+ 1) +ℤ Fixed.thirdTurnCharacter j
ellipticOrder3IsOnePlusThirdTurnCharacter zero = refl
ellipticOrder3IsOnePlusThirdTurnCharacter (suc zero) = refl
ellipticOrder3IsOnePlusThirdTurnCharacter (suc (suc zero)) = refl
ellipticOrder3IsOnePlusThirdTurnCharacter (suc (suc (suc j))) =
  ellipticOrder3IsOnePlusThirdTurnCharacter j

representationEllipticOrder2 :
  Matrix.OddPrimeCandidateUnder72 → Nat
representationEllipticOrder2 prime =
  ellipticOrder2FromJ
    (Spin.jNat (Matrix.primeAngularMomentum prime))

representationEllipticOrder3 :
  Matrix.OddPrimeCandidateUnder72 → Nat
representationEllipticOrder3 prime =
  ellipticOrder3FromJ
    (Spin.jNat (Matrix.primeAngularMomentum prime))

representationEllipticOrder2MatchesFricke :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationEllipticOrder2 prime
  ≡ Fricke.ellipticOrder2Count (Fricke.frickeRow prime)
representationEllipticOrder2MatchesFricke Matrix.prime3 = refl
representationEllipticOrder2MatchesFricke Matrix.prime5 = refl
representationEllipticOrder2MatchesFricke Matrix.prime7 = refl
representationEllipticOrder2MatchesFricke Matrix.prime11 = refl
representationEllipticOrder2MatchesFricke Matrix.prime13 = refl
representationEllipticOrder2MatchesFricke Matrix.prime17 = refl
representationEllipticOrder2MatchesFricke Matrix.prime19 = refl
representationEllipticOrder2MatchesFricke Matrix.prime23 = refl
representationEllipticOrder2MatchesFricke Matrix.prime29 = refl
representationEllipticOrder2MatchesFricke Matrix.prime31 = refl
representationEllipticOrder2MatchesFricke Matrix.prime37 = refl
representationEllipticOrder2MatchesFricke Matrix.prime41 = refl
representationEllipticOrder2MatchesFricke Matrix.prime43 = refl
representationEllipticOrder2MatchesFricke Matrix.prime47 = refl
representationEllipticOrder2MatchesFricke Matrix.prime53 = refl
representationEllipticOrder2MatchesFricke Matrix.prime59 = refl
representationEllipticOrder2MatchesFricke Matrix.prime61 = refl
representationEllipticOrder2MatchesFricke Matrix.prime67 = refl
representationEllipticOrder2MatchesFricke Matrix.prime71 = refl

representationEllipticOrder3MatchesFricke :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationEllipticOrder3 prime
  ≡ Fricke.ellipticOrder3Count (Fricke.frickeRow prime)
representationEllipticOrder3MatchesFricke Matrix.prime3 = refl
representationEllipticOrder3MatchesFricke Matrix.prime5 = refl
representationEllipticOrder3MatchesFricke Matrix.prime7 = refl
representationEllipticOrder3MatchesFricke Matrix.prime11 = refl
representationEllipticOrder3MatchesFricke Matrix.prime13 = refl
representationEllipticOrder3MatchesFricke Matrix.prime17 = refl
representationEllipticOrder3MatchesFricke Matrix.prime19 = refl
representationEllipticOrder3MatchesFricke Matrix.prime23 = refl
representationEllipticOrder3MatchesFricke Matrix.prime29 = refl
representationEllipticOrder3MatchesFricke Matrix.prime31 = refl
representationEllipticOrder3MatchesFricke Matrix.prime37 = refl
representationEllipticOrder3MatchesFricke Matrix.prime41 = refl
representationEllipticOrder3MatchesFricke Matrix.prime43 = refl
representationEllipticOrder3MatchesFricke Matrix.prime47 = refl
representationEllipticOrder3MatchesFricke Matrix.prime53 = refl
representationEllipticOrder3MatchesFricke Matrix.prime59 = refl
representationEllipticOrder3MatchesFricke Matrix.prime61 = refl
representationEllipticOrder3MatchesFricke Matrix.prime67 = refl
representationEllipticOrder3MatchesFricke Matrix.prime71 = refl

------------------------------------------------------------------------
-- Reconstruct the ordinary modular-curve genus from representation data.
------------------------------------------------------------------------

representationX0Genus :
  Matrix.OddPrimeCandidateUnder72 → Nat
representationX0Genus prime =
  ((Matrix.primeLevel prime + 1)
    ∸ 3 * representationEllipticOrder2 prime
    ∸ 4 * representationEllipticOrder3 prime)
  / 12

representationX0GenusMatchesFricke :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationX0Genus prime
  ≡ Fricke.genusX0 (Fricke.frickeRow prime)
representationX0GenusMatchesFricke Matrix.prime3 = refl
representationX0GenusMatchesFricke Matrix.prime5 = refl
representationX0GenusMatchesFricke Matrix.prime7 = refl
representationX0GenusMatchesFricke Matrix.prime11 = refl
representationX0GenusMatchesFricke Matrix.prime13 = refl
representationX0GenusMatchesFricke Matrix.prime17 = refl
representationX0GenusMatchesFricke Matrix.prime19 = refl
representationX0GenusMatchesFricke Matrix.prime23 = refl
representationX0GenusMatchesFricke Matrix.prime29 = refl
representationX0GenusMatchesFricke Matrix.prime31 = refl
representationX0GenusMatchesFricke Matrix.prime37 = refl
representationX0GenusMatchesFricke Matrix.prime41 = refl
representationX0GenusMatchesFricke Matrix.prime43 = refl
representationX0GenusMatchesFricke Matrix.prime47 = refl
representationX0GenusMatchesFricke Matrix.prime53 = refl
representationX0GenusMatchesFricke Matrix.prime59 = refl
representationX0GenusMatchesFricke Matrix.prime61 = refl
representationX0GenusMatchesFricke Matrix.prime67 = refl
representationX0GenusMatchesFricke Matrix.prime71 = refl

representationX0GenusFormula :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  12 * representationX0Genus prime
    + 3 * representationEllipticOrder2 prime
    + 4 * representationEllipticOrder3 prime
  ≡ Matrix.primeLevel prime + 1
representationX0GenusFormula Matrix.prime3 = refl
representationX0GenusFormula Matrix.prime5 = refl
representationX0GenusFormula Matrix.prime7 = refl
representationX0GenusFormula Matrix.prime11 = refl
representationX0GenusFormula Matrix.prime13 = refl
representationX0GenusFormula Matrix.prime17 = refl
representationX0GenusFormula Matrix.prime19 = refl
representationX0GenusFormula Matrix.prime23 = refl
representationX0GenusFormula Matrix.prime29 = refl
representationX0GenusFormula Matrix.prime31 = refl
representationX0GenusFormula Matrix.prime37 = refl
representationX0GenusFormula Matrix.prime41 = refl
representationX0GenusFormula Matrix.prime43 = refl
representationX0GenusFormula Matrix.prime47 = refl
representationX0GenusFormula Matrix.prime53 = refl
representationX0GenusFormula Matrix.prime59 = refl
representationX0GenusFormula Matrix.prime61 = refl
representationX0GenusFormula Matrix.prime67 = refl
representationX0GenusFormula Matrix.prime71 = refl

------------------------------------------------------------------------
-- Representation + arithmetic Fricke closure defect.
------------------------------------------------------------------------

representationArithmeticFrickeDefect :
  Matrix.OddPrimeCandidateUnder72 → Nat
representationArithmeticFrickeDefect prime =
  (2 * representationX0Genus prime + 2)
  ∸ Fricke.frickeFixedPointCount (Fricke.frickeRow prime)

representationArithmeticDefectIsFourTimesFrickeGenus :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationArithmeticFrickeDefect prime
  ≡ 4 * Fricke.genusX0Plus (Fricke.frickeRow prime)
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime3 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime5 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime7 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime11 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime13 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime17 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime19 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime23 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime29 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime31 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime37 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime41 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime43 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime47 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime53 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime59 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime61 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime67 = refl
representationArithmeticDefectIsFourTimesFrickeGenus Matrix.prime71 = refl

representationArithmeticFrickeClosed :
  Matrix.OddPrimeCandidateUnder72 → Bool
representationArithmeticFrickeClosed prime =
  Fricke.isZero (representationArithmeticFrickeDefect prime)

coupledClosureMatchesFrickeGenusZero :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationArithmeticFrickeClosed prime
  ≡ Fricke.frickeGenusZero prime
coupledClosureMatchesFrickeGenusZero Matrix.prime3 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime5 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime7 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime11 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime13 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime17 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime19 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime23 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime29 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime31 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime37 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime41 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime43 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime47 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime53 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime59 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime61 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime67 = refl
coupledClosureMatchesFrickeGenusZero Matrix.prime71 = refl

coupledClosureMatchesExternalOggOnScan :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationArithmeticFrickeClosed prime
  ≡ Matrix.externalOggLabel prime
coupledClosureMatchesExternalOggOnScan prime =
  trans
    (coupledClosureMatchesFrickeGenusZero prime)
    (Fricke.frickeGenusZeroMatchesExternalOggLabel prime)

prime37CoupledDefectIsFour :
  representationArithmeticFrickeDefect Matrix.prime37 ≡ 4
prime37CoupledDefectIsFour = refl

prime43CoupledDefectIsFour :
  representationArithmeticFrickeDefect Matrix.prime43 ≡ 4
prime43CoupledDefectIsFour = refl

prime53CoupledDefectIsFour :
  representationArithmeticFrickeDefect Matrix.prime53 ≡ 4
prime53CoupledDefectIsFour = refl

prime61CoupledDefectIsFour :
  representationArithmeticFrickeDefect Matrix.prime61 ≡ 4
prime61CoupledDefectIsFour = refl

prime67CoupledDefectIsEight :
  representationArithmeticFrickeDefect Matrix.prime67 ≡ 8
prime67CoupledDefectIsEight = refl

record PrimeRepresentationFrickeCouplingBoundary : Set where
  field
    ellipticCountsDerivedFromSO3Characters : Bool
    ellipticCountsDerivedFromSO3CharactersIsTrue :
      ellipticCountsDerivedFromSO3Characters ≡ true
    x0GenusReconstructedFromRepresentationData : Bool
    x0GenusReconstructedFromRepresentationDataIsTrue :
      x0GenusReconstructedFromRepresentationData ≡ true
    frickeClosureUsesArithmeticClassNumberFixedPoints : Bool
    frickeClosureUsesArithmeticClassNumberFixedPointsIsTrue :
      frickeClosureUsesArithmeticClassNumberFixedPoints ≡ true
    coupledDefectMatchesFourTimesFrickeGenusOnScan : Bool
    coupledDefectMatchesFourTimesFrickeGenusOnScanIsTrue :
      coupledDefectMatchesFourTimesFrickeGenusOnScan ≡ true
    representationDataAloneClaimedToSelectOgg : Bool
    representationDataAloneClaimedToSelectOggIsFalse :
      representationDataAloneClaimedToSelectOgg ≡ false
    globalOggTheoremClaimed : Bool
    globalOggTheoremClaimedIsFalse :
      globalOggTheoremClaimed ≡ false

canonicalPrimeRepresentationFrickeCouplingBoundary :
  PrimeRepresentationFrickeCouplingBoundary
canonicalPrimeRepresentationFrickeCouplingBoundary =
  record
    { ellipticCountsDerivedFromSO3Characters = true
    ; ellipticCountsDerivedFromSO3CharactersIsTrue = refl
    ; x0GenusReconstructedFromRepresentationData = true
    ; x0GenusReconstructedFromRepresentationDataIsTrue = refl
    ; frickeClosureUsesArithmeticClassNumberFixedPoints = true
    ; frickeClosureUsesArithmeticClassNumberFixedPointsIsTrue = refl
    ; coupledDefectMatchesFourTimesFrickeGenusOnScan = true
    ; coupledDefectMatchesFourTimesFrickeGenusOnScanIsTrue = refl
    ; representationDataAloneClaimedToSelectOgg = false
    ; representationDataAloneClaimedToSelectOggIsFalse = refl
    ; globalOggTheoremClaimed = false
    ; globalOggTheoremClaimedIsFalse = refl
    }
