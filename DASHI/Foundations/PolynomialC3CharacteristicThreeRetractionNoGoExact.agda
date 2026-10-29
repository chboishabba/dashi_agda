module DASHI.Foundations.PolynomialC3CharacteristicThreeRetractionNoGoExact where

------------------------------------------------------------------------
-- NO EQUIVARIANT LINEAR RETRACTION OF F3[C3] ONTO ITS CONSTANT LINE.
--
-- A C3-invariant F3-linear functional on the three-point permutation
-- module has the same coefficient at each cyclically permuted basis
-- vector: a=b=c. Applying it to constant vector (1,1,1) yields
-- 3*a=0 mod3, but a retraction onto the constant line would require
-- this value to be 1. Contradiction.
--
-- Hence the characteristic-zero trivial⊕standard3-point split
-- (basis determinant THREE) must NOT be promoted over F3.
-- This is a finite algebraic theorem, not Maschke in full generality,
-- and is different from valid F3 splitting for C2 reflection since
-- 2 is invertible modulo 3.
--
-- Original classical group/representation theory and original DASHI
-- Phase3 C3 addition owner retained. New no-go source owner #1414.
-- AGDA SOURCE WRITTEN / KERNEL NOT VERIFIED.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact as C3

tripleSumZero :
  (a : Phase.Phase3) →
  C3._+₃_ a (C3._+₃_ a a) ≡ Phase.phase0
tripleSumZero Phase.phase0 = refl
tripleSumZero Phase.phase1 = refl
tripleSumZero Phase.phase2 = refl

tripleSumCannotBeOne :
  (a : Phase.Phase3) →
  C3._+₃_ a (C3._+₃_ a a) ≡ Phase.phase1 → ⊥
tripleSumCannotBeOne Phase.phase0 ()
tripleSumCannotBeOne Phase.phase1 ()
tripleSumCannotBeOne Phase.phase2 ()

-- The only input assumptions are the C3-invariance constraints
-- on a linear functional's three basis coefficients. They force
-- equality at each cyclic basis vector. A retraction would
-- additionally require the constant vector to evaluate to 1.
noC3InvariantLinearFunctionalRetraction :
  (a b c : Phase.Phase3) →
  a ≡ b →
  b ≡ c →
  C3._+₃_ a (C3._+₃_ b c) ≡ Phase.phase1 →
  ⊥
noC3InvariantLinearFunctionalRetraction a .a .a refl refl fixed =
  tripleSumCannotBeOne a fixed

-- This excludes all linear equivariant retractions onto the
-- constant line, not arbitrary nonlinear chosen-representative
-- orbit sampling. It does NOT contradict the separate C2
-- 7-even+4-odd F3 Fourier decomposition on 11 C3 orbits.
