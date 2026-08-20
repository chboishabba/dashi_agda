module DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshMobiusSeparationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Gian-Carlo Rota, "On the Foundations of Combinatorial Theory I. Theory of
-- Mobius Functions", Z. Wahrscheinlichkeitstheorie verw. Gebiete 2 (1964),
-- 340--368. DOI: 10.1007/BF00531932.
--
-- Jean-Pierre Serre, "Linear Representations of Finite Groups",
-- Springer, 1977. DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- The selected-region G2 calculation already uses the incidence algebra of
-- the sixteen subsets.  The same set also supports Walsh characters after
-- interpreting subsets as sign masks.  These are distinct structures.
--
-- This file proves two sharp guards:
--
--   1. the Mobius and Walsh transforms disagree on a literal source function;
--   2. even full adjacent-coordinate permutation/degree invariance of a Green
--      kernel does NOT imply dependence only on symmetric difference.
--
-- Therefore the existing 4+6+4+1 degree collapse cannot be promoted to Walsh
-- diagonalisation without a genuinely stronger physical kernel theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Empty using (⊥)
open import Data.Rational using (1ℚ; -_)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeMobiusExact as Mobius
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact as Walsh

------------------------------------------------------------------------
-- Literal transform separation.
------------------------------------------------------------------------

emptySpikeMobiusS0 :
  Mobius.mobiusAtom Walsh.emptySpike Cube.s0 ≡ - 1ℚ
emptySpikeMobiusS0 = refl

walshIsNotMobiusOnSameCarrier :
  Walsh.walshCoefficient Walsh.emptySpike Cube.s0
  ≡ Mobius.mobiusAtom Walsh.emptySpike Cube.s0 → ⊥
walshIsNotMobiusOnSameCarrier ()

------------------------------------------------------------------------
-- S4 adjacent-coordinate action on Subset4.
------------------------------------------------------------------------

data AdjacentPermutation4 : Set where
  swap01 swap12 swap23 : AdjacentPermutation4

permuteSubset : AdjacentPermutation4 → Cube.Subset4 → Cube.Subset4
permuteSubset swap01 Cube.empty = Cube.empty
permuteSubset swap01 Cube.s0 = Cube.s1
permuteSubset swap01 Cube.s1 = Cube.s0
permuteSubset swap01 Cube.s2 = Cube.s2
permuteSubset swap01 Cube.s3 = Cube.s3
permuteSubset swap01 Cube.s01 = Cube.s01
permuteSubset swap01 Cube.s02 = Cube.s12
permuteSubset swap01 Cube.s03 = Cube.s13
permuteSubset swap01 Cube.s12 = Cube.s02
permuteSubset swap01 Cube.s13 = Cube.s03
permuteSubset swap01 Cube.s23 = Cube.s23
permuteSubset swap01 Cube.s012 = Cube.s012
permuteSubset swap01 Cube.s013 = Cube.s013
permuteSubset swap01 Cube.s023 = Cube.s123
permuteSubset swap01 Cube.s123 = Cube.s023
permuteSubset swap01 Cube.s0123 = Cube.s0123

permuteSubset swap12 Cube.empty = Cube.empty
permuteSubset swap12 Cube.s0 = Cube.s0
permuteSubset swap12 Cube.s1 = Cube.s2
permuteSubset swap12 Cube.s2 = Cube.s1
permuteSubset swap12 Cube.s3 = Cube.s3
permuteSubset swap12 Cube.s01 = Cube.s02
permuteSubset swap12 Cube.s02 = Cube.s01
permuteSubset swap12 Cube.s03 = Cube.s03
permuteSubset swap12 Cube.s12 = Cube.s12
permuteSubset swap12 Cube.s13 = Cube.s23
permuteSubset swap12 Cube.s23 = Cube.s13
permuteSubset swap12 Cube.s012 = Cube.s012
permuteSubset swap12 Cube.s013 = Cube.s023
permuteSubset swap12 Cube.s023 = Cube.s013
permuteSubset swap12 Cube.s123 = Cube.s123
permuteSubset swap12 Cube.s0123 = Cube.s0123

permuteSubset swap23 Cube.empty = Cube.empty
permuteSubset swap23 Cube.s0 = Cube.s0
permuteSubset swap23 Cube.s1 = Cube.s1
permuteSubset swap23 Cube.s2 = Cube.s3
permuteSubset swap23 Cube.s3 = Cube.s2
permuteSubset swap23 Cube.s01 = Cube.s01
permuteSubset swap23 Cube.s02 = Cube.s03
permuteSubset swap23 Cube.s03 = Cube.s02
permuteSubset swap23 Cube.s12 = Cube.s13
permuteSubset swap23 Cube.s13 = Cube.s12
permuteSubset swap23 Cube.s23 = Cube.s23
permuteSubset swap23 Cube.s012 = Cube.s013
permuteSubset swap23 Cube.s013 = Cube.s012
permuteSubset swap23 Cube.s023 = Cube.s023
permuteSubset swap23 Cube.s123 = Cube.s123
permuteSubset swap23 Cube.s0123 = Cube.s0123

degreeValue : Cube.Subset4 → Nat
degreeValue Cube.empty = 0
degreeValue Cube.s0 = 1
degreeValue Cube.s1 = 1
degreeValue Cube.s2 = 1
degreeValue Cube.s3 = 1
degreeValue Cube.s01 = 2
degreeValue Cube.s02 = 2
degreeValue Cube.s03 = 2
degreeValue Cube.s12 = 2
degreeValue Cube.s13 = 2
degreeValue Cube.s23 = 2
degreeValue Cube.s012 = 3
degreeValue Cube.s013 = 3
degreeValue Cube.s023 = 3
degreeValue Cube.s123 = 3
degreeValue Cube.s0123 = 4

degreePermutationInvariant :
  (permutation : AdjacentPermutation4) →
  (subset : Cube.Subset4) →
  degreeValue (permuteSubset permutation subset) ≡ degreeValue subset
degreePermutationInvariant swap01 Cube.empty = refl
degreePermutationInvariant swap01 Cube.s0 = refl
degreePermutationInvariant swap01 Cube.s1 = refl
degreePermutationInvariant swap01 Cube.s2 = refl
degreePermutationInvariant swap01 Cube.s3 = refl
degreePermutationInvariant swap01 Cube.s01 = refl
degreePermutationInvariant swap01 Cube.s02 = refl
degreePermutationInvariant swap01 Cube.s03 = refl
degreePermutationInvariant swap01 Cube.s12 = refl
degreePermutationInvariant swap01 Cube.s13 = refl
degreePermutationInvariant swap01 Cube.s23 = refl
degreePermutationInvariant swap01 Cube.s012 = refl
degreePermutationInvariant swap01 Cube.s013 = refl
degreePermutationInvariant swap01 Cube.s023 = refl
degreePermutationInvariant swap01 Cube.s123 = refl
degreePermutationInvariant swap01 Cube.s0123 = refl
degreePermutationInvariant swap12 Cube.empty = refl
degreePermutationInvariant swap12 Cube.s0 = refl
degreePermutationInvariant swap12 Cube.s1 = refl
degreePermutationInvariant swap12 Cube.s2 = refl
degreePermutationInvariant swap12 Cube.s3 = refl
degreePermutationInvariant swap12 Cube.s01 = refl
degreePermutationInvariant swap12 Cube.s02 = refl
degreePermutationInvariant swap12 Cube.s03 = refl
degreePermutationInvariant swap12 Cube.s12 = refl
degreePermutationInvariant swap12 Cube.s13 = refl
degreePermutationInvariant swap12 Cube.s23 = refl
degreePermutationInvariant swap12 Cube.s012 = refl
degreePermutationInvariant swap12 Cube.s013 = refl
degreePermutationInvariant swap12 Cube.s023 = refl
degreePermutationInvariant swap12 Cube.s123 = refl
degreePermutationInvariant swap12 Cube.s0123 = refl
degreePermutationInvariant swap23 Cube.empty = refl
degreePermutationInvariant swap23 Cube.s0 = refl
degreePermutationInvariant swap23 Cube.s1 = refl
degreePermutationInvariant swap23 Cube.s2 = refl
degreePermutationInvariant swap23 Cube.s3 = refl
degreePermutationInvariant swap23 Cube.s01 = refl
degreePermutationInvariant swap23 Cube.s02 = refl
degreePermutationInvariant swap23 Cube.s03 = refl
degreePermutationInvariant swap23 Cube.s12 = refl
degreePermutationInvariant swap23 Cube.s13 = refl
degreePermutationInvariant swap23 Cube.s23 = refl
degreePermutationInvariant swap23 Cube.s012 = refl
degreePermutationInvariant swap23 Cube.s013 = refl
degreePermutationInvariant swap23 Cube.s023 = refl
degreePermutationInvariant swap23 Cube.s123 = refl
degreePermutationInvariant swap23 Cube.s0123 = refl

degreeKernel : Cube.Subset4 → Cube.Subset4 → Nat
degreeKernel left right = degreeValue left * degreeValue right

degreeKernelPermutationInvariant :
  (permutation : AdjacentPermutation4) →
  (left right : Cube.Subset4) →
  degreeKernel (permuteSubset permutation left) (permuteSubset permutation right)
  ≡ degreeKernel left right
degreeKernelPermutationInvariant permutation left right =
  cong₂ _*_
    (degreePermutationInvariant permutation left)
    (degreePermutationInvariant permutation right)

------------------------------------------------------------------------
-- A necessary two-point consequence of XOR-convolution structure.
-- Both (empty,empty) and (s0,s0) have symmetric difference empty, so any
-- kernel K(S,T)=g(S xor T) must assign them the same value.
------------------------------------------------------------------------

record XorConvolutionNecessaryDiagonal
    (kernel : Cube.Subset4 → Cube.Subset4 → Nat) : Set₁ where
  field
    profileAtEmpty : Nat
    emptyDiagonalUsesProfile :
      kernel Cube.empty Cube.empty ≡ profileAtEmpty
    s0DiagonalUsesSameProfile :
      kernel Cube.s0 Cube.s0 ≡ profileAtEmpty

open XorConvolutionNecessaryDiagonal public

degreeKernelEmptyDiagonal : degreeKernel Cube.empty Cube.empty ≡ zero
degreeKernelEmptyDiagonal = refl

degreeKernelS0Diagonal : degreeKernel Cube.s0 Cube.s0 ≡ suc zero
degreeKernelS0Diagonal = refl

zeroNotOne : zero ≡ suc zero → ⊥
zeroNotOne ()

degreeSymmetryDoesNotImplyXorConvolution :
  XorConvolutionNecessaryDiagonal degreeKernel → ⊥
degreeSymmetryDoesNotImplyXorConvolution evidence =
  zeroNotOne
    (trans
      (sym degreeKernelEmptyDiagonal)
      (trans
        (emptyDiagonalUsesProfile evidence)
        (trans
          (sym (s0DiagonalUsesSameProfile evidence))
          degreeKernelS0Diagonal)))

booleanFourCubeWalshMobiusSeparatedLevel : ProofLevel
booleanFourCubeWalshMobiusSeparatedLevel = machineChecked

degreePermutationSymmetryNotEnoughForWalshLevel : ProofLevel
degreePermutationSymmetryNotEnoughForWalshLevel = machineChecked

-- The actual selected Green kernel may still possess the stronger structure;
-- it simply cannot be inferred from the already-proved degree grouping.
selectedGreenXorConvolutionOrStrongerCharacterEquivarianceLevel : ProofLevel
selectedGreenXorConvolutionOrStrongerCharacterEquivarianceLevel = conditional
