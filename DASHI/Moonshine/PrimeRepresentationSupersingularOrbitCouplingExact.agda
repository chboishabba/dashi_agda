module DASHI.Moonshine.PrimeRepresentationSupersingularOrbitCouplingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
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
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Compose the SO(3)-derived X0 genus with the repository's exact finite
-- supersingular/Frobenius orbit normal form.
--
-- The representation side determines
--
--   total supersingular slots = g_rep(X0(p)) + 1,
--
-- because g_rep is reconstructed from p=dim(V_j) and the order-two/order-
-- three SO(3) characters.  The arithmetic class-number side determines
--
--   rational/fixed slots = r_p/2.
--
-- The leftover slots come in Frobenius two-orbits, and their number is exactly
--
--   g(X0+(p)) = D_rep+arith(p)/4.
--
-- Thus the finite control scan has an explicit division of labour:
--
--   continuous representation data -> total orbit budget,
--   arithmetic class numbers       -> fixed-slot budget,
--   their deficit                   -> conjugate Frobenius pairs.
--
-- No actual supersingular elliptic-curve carrier or geometric Frobenius map is
-- manufactured here; the realization boundary of
-- SupersingularFrobeniusOrbitSpectrumExact remains intact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Nat using (_/_)

import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeOrbitSaturationExact as Saturation
import DASHI.Moonshine.PrimeRepresentationFrickeCouplingExact as Coupling
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Frobenius

representationSupersingularTotal :
  Matrix.OddPrimeCandidateUnder72 → Nat
representationSupersingularTotal prime =
  Coupling.representationX0Genus prime + 1

representationTotalMatchesSupersingularTotal :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationSupersingularTotal prime
  ≡ Frobenius.totalSupersingularCount prime
representationTotalMatchesSupersingularTotal prime =
  cong (λ genus → genus + 1)
    (Coupling.representationX0GenusMatchesFricke prime)

representationFrobeniusTwoOrbitCount :
  Matrix.OddPrimeCandidateUnder72 → Nat
representationFrobeniusTwoOrbitCount prime =
  Coupling.representationArithmeticFrickeDefect prime / 4

representationPairCountMatchesFrobenius :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationFrobeniusTwoOrbitCount prime
  ≡ Frobenius.frobeniusTwoOrbitCount prime
representationPairCountMatchesFrobenius Matrix.prime3 = refl
representationPairCountMatchesFrobenius Matrix.prime5 = refl
representationPairCountMatchesFrobenius Matrix.prime7 = refl
representationPairCountMatchesFrobenius Matrix.prime11 = refl
representationPairCountMatchesFrobenius Matrix.prime13 = refl
representationPairCountMatchesFrobenius Matrix.prime17 = refl
representationPairCountMatchesFrobenius Matrix.prime19 = refl
representationPairCountMatchesFrobenius Matrix.prime23 = refl
representationPairCountMatchesFrobenius Matrix.prime29 = refl
representationPairCountMatchesFrobenius Matrix.prime31 = refl
representationPairCountMatchesFrobenius Matrix.prime37 = refl
representationPairCountMatchesFrobenius Matrix.prime41 = refl
representationPairCountMatchesFrobenius Matrix.prime43 = refl
representationPairCountMatchesFrobenius Matrix.prime47 = refl
representationPairCountMatchesFrobenius Matrix.prime53 = refl
representationPairCountMatchesFrobenius Matrix.prime59 = refl
representationPairCountMatchesFrobenius Matrix.prime61 = refl
representationPairCountMatchesFrobenius Matrix.prime67 = refl
representationPairCountMatchesFrobenius Matrix.prime71 = refl

representationSupersingularOrbitBalance :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationSupersingularTotal prime
  ≡ Frobenius.rationalSupersingularCount prime
    + 2 * representationFrobeniusTwoOrbitCount prime
representationSupersingularOrbitBalance prime =
  trans
    (representationTotalMatchesSupersingularTotal prime)
    (trans
      (Frobenius.supersingularOrbitCountExact prime)
      (cong
        (λ paired → Frobenius.rationalSupersingularCount prime + 2 * paired)
        (sym (representationPairCountMatchesFrobenius prime))))

representationAllSupersingularSlotsFixed :
  Matrix.OddPrimeCandidateUnder72 → Bool
representationAllSupersingularSlotsFixed prime =
  Coupling.representationArithmeticFrickeClosed prime

representationAllFixedMatchesFrobenius :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationAllSupersingularSlotsFixed prime
  ≡ Frobenius.allSupersingularSlotsFixed prime
representationAllFixedMatchesFrobenius prime =
  trans
    (Coupling.coupledClosureMatchesFrickeGenusZero prime)
    (sym
      (trans
        (Frobenius.allFixedMatchesFrickeSaturation prime)
        (Saturation.saturationMatchesGenusZero prime)))

prime37RepresentationOrbitBalance :
  representationSupersingularTotal Matrix.prime37
  ≡ 1 + 2 * 1
prime37RepresentationOrbitBalance = refl

prime43RepresentationOrbitBalance :
  representationSupersingularTotal Matrix.prime43
  ≡ 2 + 2 * 1
prime43RepresentationOrbitBalance = refl

prime67RepresentationOrbitBalance :
  representationSupersingularTotal Matrix.prime67
  ≡ 2 + 2 * 2
prime67RepresentationOrbitBalance = refl

prime71RepresentationOrbitBalance :
  representationSupersingularTotal Matrix.prime71
  ≡ 7 + 2 * 0
prime71RepresentationOrbitBalance = refl

record PrimeRepresentationSupersingularOrbitBoundary : Set where
  field
    representationDeterminesTotalSlotBudget : Bool
    representationDeterminesTotalSlotBudgetIsTrue :
      representationDeterminesTotalSlotBudget ≡ true
    arithmeticClassNumbersDetermineFixedSlotBudget : Bool
    arithmeticClassNumbersDetermineFixedSlotBudgetIsTrue :
      arithmeticClassNumbersDetermineFixedSlotBudget ≡ true
    coupledDefectDeterminesFrobeniusPairCount : Bool
    coupledDefectDeterminesFrobeniusPairCountIsTrue :
      coupledDefectDeterminesFrobeniusPairCount ≡ true
    actualGeometricFrobeniusConstructedHere : Bool
    actualGeometricFrobeniusConstructedHereIsFalse :
      actualGeometricFrobeniusConstructedHere ≡ false

canonicalPrimeRepresentationSupersingularOrbitBoundary :
  PrimeRepresentationSupersingularOrbitBoundary
canonicalPrimeRepresentationSupersingularOrbitBoundary =
  record
    { representationDeterminesTotalSlotBudget = true
    ; representationDeterminesTotalSlotBudgetIsTrue = refl
    ; arithmeticClassNumbersDetermineFixedSlotBudget = true
    ; arithmeticClassNumbersDetermineFixedSlotBudgetIsTrue = refl
    ; coupledDefectDeterminesFrobeniusPairCount = true
    ; coupledDefectDeterminesFrobeniusPairCountIsTrue = refl
    ; actualGeometricFrobeniusConstructedHere = false
    ; actualGeometricFrobeniusConstructedHereIsFalse = refl
    }
