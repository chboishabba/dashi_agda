module DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Ryan O'Donnell,
-- "Analysis of Boolean Functions", Cambridge University Press, 2014.
-- DOI: 10.1017/CBO9781139814782.
-- Chapter 1: "Boolean Functions and the Fourier Expansion",
-- DOI: 10.1017/CBO9781139814782.002.
-- This is the standard harmonic-analysis-on-the-cube source for the
-- Walsh--Fourier convention and orthogonality of nontrivial characters.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Z. Wahrscheinlichkeitstheorie verw. Gebiete 2 (1964),
-- 340--368. DOI: 10.1007/BF00531932.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical
-- Physics 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- Put the SAME literal sixteen-element Subset4 carrier used by the G2
-- incidence/Möbius calculation under its independent (C2)^4 Walsh--Fourier
-- character geometry.  A subset A labels
--
--   chi_A(epsilon) = product_{mu in A} epsilon_mu.
--
-- This module deliberately does not identify the Boolean-lattice Möbius
-- transform with the Walsh--Fourier transform.  It gives the character layer
-- needed to test whether a physical kernel has the additional translation/XOR
-- symmetry required for Fourier diagonalisation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _/_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube

minusOne : ℚ
minusOne = - 1ℚ

bitSign : Bool → ℚ
bitSign false = 1ℚ
bitSign true = minusOne

selectedFactor : Cube.BondSlot4 → Cube.Subset4 → Cube.Subset4 → ℚ
selectedFactor slot character signMask with Cube.contains slot character
... | false = 1ℚ
... | true = bitSign (Cube.contains slot signMask)

walshCharacter : Cube.Subset4 → Cube.Subset4 → ℚ
walshCharacter character signMask =
  selectedFactor Cube.slot0 character signMask
  * selectedFactor Cube.slot1 character signMask
  * selectedFactor Cube.slot2 character signMask
  * selectedFactor Cube.slot3 character signMask

walshCoefficient : (Cube.Subset4 → ℚ) → Cube.Subset4 → ℚ
walshCoefficient value character =
  Sums.sumRational Cube.allSubsets4
    (λ signMask → walshCharacter character signMask * value signMask)

walshTrivialCoefficientIsTotal :
  (value : Cube.Subset4 → ℚ) →
  walshCoefficient value Cube.empty
  ≡ Sums.sumRational Cube.allSubsets4 value
walshTrivialCoefficientIsTotal value =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)

data NontrivialWalshCharacter : Cube.Subset4 → Set where
  nt0 : NontrivialWalshCharacter Cube.s0
  nt1 : NontrivialWalshCharacter Cube.s1
  nt2 : NontrivialWalshCharacter Cube.s2
  nt3 : NontrivialWalshCharacter Cube.s3
  nt01 : NontrivialWalshCharacter Cube.s01
  nt02 : NontrivialWalshCharacter Cube.s02
  nt03 : NontrivialWalshCharacter Cube.s03
  nt12 : NontrivialWalshCharacter Cube.s12
  nt13 : NontrivialWalshCharacter Cube.s13
  nt23 : NontrivialWalshCharacter Cube.s23
  nt012 : NontrivialWalshCharacter Cube.s012
  nt013 : NontrivialWalshCharacter Cube.s013
  nt023 : NontrivialWalshCharacter Cube.s023
  nt123 : NontrivialWalshCharacter Cube.s123
  nt0123 : NontrivialWalshCharacter Cube.s0123

constantFunction : ℚ → Cube.Subset4 → ℚ
constantFunction value signMask = value

nontrivialWalshKillsConstant :
  ∀ {character} →
  NontrivialWalshCharacter character →
  (value : ℚ) →
  walshCoefficient (constantFunction value) character ≡ 0ℚ
nontrivialWalshKillsConstant nt0 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt1 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt2 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt3 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt01 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt02 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt03 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt12 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt13 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt23 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt012 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt013 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt023 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt123 value = ℚRing.solve-∀ value
nontrivialWalshKillsConstant nt0123 value = ℚRing.solve-∀ value

trivialWalshConstantIsSixteen :
  (value : ℚ) →
  walshCoefficient (constantFunction value) Cube.empty
  ≡ (+ 16 / 1) * value
trivialWalshConstantIsSixteen value = ℚRing.solve-∀ value

------------------------------------------------------------------------
-- Exact separation from the incidence/Möbius transform.
------------------------------------------------------------------------

emptySpike : Cube.Subset4 → ℚ
emptySpike Cube.empty = 1ℚ
emptySpike Cube.s0 = 0ℚ
emptySpike Cube.s1 = 0ℚ
emptySpike Cube.s2 = 0ℚ
emptySpike Cube.s3 = 0ℚ
emptySpike Cube.s01 = 0ℚ
emptySpike Cube.s02 = 0ℚ
emptySpike Cube.s03 = 0ℚ
emptySpike Cube.s12 = 0ℚ
emptySpike Cube.s13 = 0ℚ
emptySpike Cube.s23 = 0ℚ
emptySpike Cube.s012 = 0ℚ
emptySpike Cube.s013 = 0ℚ
emptySpike Cube.s023 = 0ℚ
emptySpike Cube.s123 = 0ℚ
emptySpike Cube.s0123 = 0ℚ

emptySpikeWalshS0 : walshCoefficient emptySpike Cube.s0 ≡ 1ℚ
emptySpikeWalshS0 = refl

booleanFourCubeWalshCharacterLevel : ProofLevel
booleanFourCubeWalshCharacterLevel = machineChecked

booleanFourCubeWalshOrthogonalityConstantLevel : ProofLevel
booleanFourCubeWalshOrthogonalityConstantLevel = machineChecked
