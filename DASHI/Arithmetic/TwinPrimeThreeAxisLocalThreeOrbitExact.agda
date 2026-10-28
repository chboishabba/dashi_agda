module DASHI.Arithmetic.TwinPrimeThreeAxisLocalThreeOrbitExact where

------------------------------------------------------------------------
-- PRIME-3 LOCAL SIEVE ON THE EXISTING 3x3x3 TERNARY CUBE
--
-- Structural sources / ownership:
--   Base369Ternary27HypervoxelFabricGeometryExact: x,y,z (3^3=27).
--   BalancedTernaryAntipodalOrbitExact: strict C2 antipode,
--     its TWO-AXIS plane has 9 states and FIVE orbit classes.
--   IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact:
--     fixed outer phase and inner-plane inversion (3 x 5 = 15).
--   CertifiedPrimePairModulusExact: actual modulus-3 twin filter.
--
-- NEW concrete arithmetic cross-pollination:
--   Fix the first balanced ternary digit x=-1 and let
--        n = -1 + 3*y + 9*z (mod 27)
--   with y,z in {-1,0,+1}. These are exactly nine DISTINCT
--   residues n≡2 (mod 3); they pass the prime-3 local twin filter.
--   The affine swap of the two prime candidates
--        n -> -n-2 (mod 27)
--   corresponds EXACTLY to the simultaneous sign antipode
--        (y,z) -> (-y,-z).
--   The resulting quotient is 1 centre + 4 pairs = FIVE orbits.
--
-- This is not an isomorphism to Monster 3B or D4 representations,
-- and its five local orbit classes do not mean five prime pairs.
-- Conway/Guy FRACTRAN and Ibrahim attribution remain separate.
-- Finite source-written Agda; kernel acceptance NOT observed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.DivMod using (_%_)

import DASHI.Foundations.SSPTritCarrier as T
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Ibrahim

-- Centered balanced ternary digit expansion, interpreted modulo 27.
-- Listing the nine Nat representatives avoids negative Nat underflow.
centeredPrimeThreeResidue : T.SSPTrit → T.SSPTrit → Nat
centeredPrimeThreeResidue T.sspNegOne T.sspNegOne = 14
centeredPrimeThreeResidue T.sspZero   T.sspNegOne = 17
centeredPrimeThreeResidue T.sspPosOne T.sspNegOne = 20
centeredPrimeThreeResidue T.sspNegOne T.sspZero   = 23
centeredPrimeThreeResidue T.sspZero   T.sspZero   = 26
centeredPrimeThreeResidue T.sspPosOne T.sspZero   = 2
centeredPrimeThreeResidue T.sspNegOne T.sspPosOne = 5
centeredPrimeThreeResidue T.sspZero   T.sspPosOne = 8
centeredPrimeThreeResidue T.sspPosOne T.sspPosOne = 11

-- These nine representatives are EXACTLY the first-coordinate=-1
-- ternary slice; x still denotes a genuine separate typed axis.
centeredPrimeThreePoint :
  T.SSPTrit → T.SSPTrit → Geometry.Ternary27Point
centeredPrimeThreePoint y z =
  Geometry.ternary27Point T.sspNegOne y z

-- Each n and n+2 avoids the modulus 3. We preserve prime 3's
-- exceptional role: this is finite local survival, NOT primality.
everyCenteredResidueIsTwoModuloThree :
  (y z : T.SSPTrit) →
  centeredPrimeThreeResidue y z % 3 ≡ 2
everyCenteredResidueIsTwoModuloThree T.sspNegOne T.sspNegOne = refl
everyCenteredResidueIsTwoModuloThree T.sspZero   T.sspNegOne = refl
everyCenteredResidueIsTwoModuloThree T.sspPosOne T.sspNegOne = refl
everyCenteredResidueIsTwoModuloThree T.sspNegOne T.sspZero = refl
everyCenteredResidueIsTwoModuloThree T.sspZero   T.sspZero = refl
everyCenteredResidueIsTwoModuloThree T.sspPosOne T.sspZero = refl
everyCenteredResidueIsTwoModuloThree T.sspNegOne T.sspPosOne = refl
everyCenteredResidueIsTwoModuloThree T.sspZero   T.sspPosOne = refl
everyCenteredResidueIsTwoModuloThree T.sspPosOne T.sspPosOne = refl

-- Prime-neighbour interchange is an AFFINE antipode about n=-1.
-- On the shifted inner plane k=(n+1)/3, it becomes strict sign.
-- The condition n + swapped(n) + 2 ≡ 0 (mod 27) is exact.
localPrimePairSwapIsInnerAntipode :
  (y z : T.SSPTrit) →
  (centeredPrimeThreeResidue y z
    + centeredPrimeThreeResidue
        (Orbit.strictAntipode y) (Orbit.strictAntipode z)
    + 2) % 27 ≡ 0
localPrimePairSwapIsInnerAntipode T.sspNegOne T.sspNegOne = refl
localPrimePairSwapIsInnerAntipode T.sspZero   T.sspNegOne = refl
localPrimePairSwapIsInnerAntipode T.sspPosOne T.sspNegOne = refl
localPrimePairSwapIsInnerAntipode T.sspNegOne T.sspZero = refl
localPrimePairSwapIsInnerAntipode T.sspZero   T.sspZero = refl
localPrimePairSwapIsInnerAntipode T.sspPosOne T.sspZero = refl
localPrimePairSwapIsInnerAntipode T.sspNegOne T.sspPosOne = refl
localPrimePairSwapIsInnerAntipode T.sspZero   T.sspPosOne = refl
localPrimePairSwapIsInnerAntipode T.sspPosOne T.sspPosOne = refl

-- Reuse the EXACT inner-inversion theorem of the original source.
primeThreeOrbitRespectsInnerInversion :
  (y z : T.SSPTrit) →
  Ibrahim.reduce27ToPhaseOrbit15
    (centeredPrimeThreePoint
      (Orbit.strictAntipode y) (Orbit.strictAntipode z))
  ≡ Ibrahim.reduce27ToPhaseOrbit15
    (centeredPrimeThreePoint y z)
primeThreeOrbitRespectsInnerInversion y z =
  Ibrahim.reduce27InnerInversionInvariant
    (centeredPrimeThreePoint y z)

nineLocalThreeSurvivors :
  Ibrahim.innerNineStateCount ≡ 9
nineLocalThreeSurvivors = Ibrahim.innerNineStateCountIsNine

fiveInnerSwapOrbitClasses :
  Orbit.antipodalClass9Count ≡ 5
fiveInnerSwapOrbitClasses = Orbit.antipodalClass9CountIsFive

nineDecomposesAsOneCentreFourSwapPairs :
  9 ≡ 1 + 4 * 2
nineDecomposesAsOneCentreFourSwapPairs =
  Orbit.nineDecomposesAsCentrePlusFourPairs

-- Explicitly keep the full outer 3-axis cube capacity distinct
-- from this prime-3 survivor slice's nine states / five orbits.
fullCubeHasTwentySevenPositions :
  Geometry.hypervoxelStateCount ≡ 27
fullCubeHasTwentySevenPositions =
  Geometry.hypervoxelStateCountIs27
