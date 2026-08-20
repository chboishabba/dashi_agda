module DASHI.Physics.YangMills.BalabanClayT4SignOrbitGlobalCancellationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977. DOI: 10.1007/978-1-4684-9458-7.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Strengthen the Round57 sign-character lane from pointwise invariance to an
-- orbit-sum theorem.  A sign orbit is parameterized by the exact Subset4
-- carrier, and a pure nontrivial character sector
--
--     signs |-> chi_A(signs) * amplitude
--
-- has zero complete orbit sum.  More generally, if a source integrand on one
-- geometric absolute-profile orbit factors as a Walsh character times a single
-- invariant amplitude, the orbit contributes exactly zero BEFORE any interval
-- arithmetic.  This is the finite change-of-variables cancellation we want to
-- exploit in the Wilson/ghost/Haar beta calculation.
--
-- We deliberately do not assert that the physical source integrand has this
-- factorization.  Producing that factorization from the literal diagram syntax
-- is the remaining source theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact as Walsh
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopSignCharacterProjectionExact as Sign

signOrbitSum :
  (Grid.GridCell4 → ℚ) → Grid.GridCell4 → ℚ
signOrbitSum value representative =
  Sums.sumRational Cube.allSubsets4
    (λ signs → value (Sign.signAct signs representative))

record CharacterFactorizationAt
    (frequency : Cube.Subset4)
    (value : Grid.GridCell4 → ℚ)
    (representative : Grid.GridCell4) : Set where
  field
    amplitude : ℚ
    factorization : ∀ signs →
      value (Sign.signAct signs representative)
      ≡ Walsh.walshCharacter frequency signs * amplitude
open CharacterFactorizationAt public

signOrbitSumFromCharacterFactorization :
  ∀ frequency value representative →
  (factorized : CharacterFactorizationAt frequency value representative) →
  signOrbitSum value representative
  ≡ Walsh.characterSectorOrbitSum frequency (amplitude factorized)
signOrbitSumFromCharacterFactorization frequency value representative factorized =
  Sums.sumRationalCong
    Cube.allSubsets4
    (λ signs → value (Sign.signAct signs representative))
    (Walsh.characterSector frequency (amplitude factorized))
    (factorization factorized)

nontrivialCharacterSignOrbitVanishes :
  ∀ {frequency} → Walsh.NontrivialFrequency frequency →
  ∀ value representative →
  CharacterFactorizationAt frequency value representative →
  signOrbitSum value representative ≡ 0ℚ
nontrivialCharacterSignOrbitVanishes nontrivial value representative factorized =
  trans
    (signOrbitSumFromCharacterFactorization _ value representative factorized)
    (Walsh.nontrivialCharacterSectorOrbitSumVanishes
      nontrivial (amplitude factorized))

signOrbitCharacterFactorizationLevel : ProofLevel
signOrbitCharacterFactorizationLevel = machineChecked

nontrivialCharacterGlobalOrbitCancellationLevel : ProofLevel
nontrivialCharacterGlobalOrbitCancellationLevel = machineChecked

-- Physical source leaf: decompose each literal regular-integrand sign orbit into
-- Walsh sectors, or at minimum prove that every nontrivial sector has the
-- CharacterFactorizationAt form above.  Only the trivial/even sector then needs
-- interval enclosure.
literalWilsonOneLoopSignOrbitSectorDecompositionLevel : ProofLevel
literalWilsonOneLoopSignOrbitSectorDecompositionLevel = conditional
