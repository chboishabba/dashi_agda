module DASHI.Physics.YangMills.BalabanPositiveKernelReflectionPositivityNoGoExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Reflection positivity and positivity of an RG/Markov transition kernel are
-- not the same theorem.  The Wilson/Osterwalder--Seiler reflection form is a
-- positive-semidefinite quadratic form across a time-reflection hyperplane.
-- By contrast, the Round59 positive-RG carrier only asks for nonnegative local
-- transition weights before linearization.
--
-- This file gives the smallest exact counterexample: an entrywise-positive
-- symmetric two-state kernel can still have a negative reflection quadratic
-- form.  Consequently lattice reflection positivity cannot be inferred from
-- PositiveLocalRGGeometry alone, and conversely the imported Wilson transfer-
-- matrix theorem does not construct the Bałaban RG transition kernel.
--
-- The point is structural rather than bibliographic; no external theorem is
-- needed for the finite counterexample.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using
  (ℤ; +_; -[1+_]; _+_; _*_; _<_; -<+)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- A positive two-state kernel matrix [[1,2],[2,1]].
------------------------------------------------------------------------

data TwoState : Set where
  state0 state1 : TwoState

positiveKernelWeight : TwoState → TwoState → Nat
positiveKernelWeight state0 state0 = 1
positiveKernelWeight state0 state1 = 2
positiveKernelWeight state1 state0 = 2
positiveKernelWeight state1 state1 = 1

rowMass : TwoState → Nat
rowMass state =
  positiveKernelWeight state state0
  + positiveKernelWeight state state1

row0MassIsThree : rowMass state0 ≡ 3
row0MassIsThree = refl

row1MassIsThree : rowMass state1 ≡ 3
row1MassIsThree = refl

kernelSymmetric : ∀ left right →
  positiveKernelWeight left right ≡ positiveKernelWeight right left
kernelSymmetric state0 state0 = refl
kernelSymmetric state0 state1 = refl
kernelSymmetric state1 state0 = refl
kernelSymmetric state1 state1 = refl

------------------------------------------------------------------------
-- Signed reflection test vector (1,-1).
------------------------------------------------------------------------

signedTest : TwoState → ℤ
signedTest state0 = + 1
signedTest state1 = -[1+ 0 ]

integerKernelWeight : TwoState → TwoState → ℤ
integerKernelWeight left right = + (positiveKernelWeight left right)

reflectionQuadraticWitness : ℤ
reflectionQuadraticWitness =
    signedTest state0 * integerKernelWeight state0 state0 * signedTest state0
  + signedTest state0 * integerKernelWeight state0 state1 * signedTest state1
  + signedTest state1 * integerKernelWeight state1 state0 * signedTest state0
  + signedTest state1 * integerKernelWeight state1 state1 * signedTest state1

-- 1 - 2 - 2 + 1 = -2.
reflectionQuadraticWitnessIsNegativeTwo :
  reflectionQuadraticWitness ≡ -[1+ 1 ]
reflectionQuadraticWitnessIsNegativeTwo = refl

reflectionQuadraticWitnessNegative :
  reflectionQuadraticWitness < + 0
reflectionQuadraticWitnessNegative
  rewrite reflectionQuadraticWitnessIsNegativeTwo = -<+

------------------------------------------------------------------------
-- Frontier consequence.
------------------------------------------------------------------------

positiveKernelDoesNotByItselfImplyReflectionPositivityLevel : ProofLevel
positiveKernelDoesNotByItselfImplyReflectionPositivityLevel = machineChecked

-- Therefore the two physical source identifications remain distinct:
--   (1) literal Wilson cross-plane reflection-square factorization;
--   (2) literal Bałaban positive RG transition/Dirichlet kernel.
-- They may share the same Wilson/Boltzmann source data, but neither follows
-- merely from the positivity property required by the other.
reflectionPositivityAndRGKernelNeedDistinctPhysicalProofsLevel : ProofLevel
reflectionPositivityAndRGKernelNeedDistinctPhysicalProofsLevel = conditional
