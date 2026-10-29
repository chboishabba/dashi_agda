module DASHI.Foundations.PolynomialC3S3TwentySevenOrbitRefinementExact where

------------------------------------------------------------------------
-- VIDEO ROOT SYMMETRY -> NATIVE REPOSITORY 27-ENDOMORPHISM ACTION.
--
-- For X=End(T3), |X|=3^3=27, S3 acts by CONJUGATION.
-- C3=A3 is the existing THREE-CYCLE subgroup.
-- Conjugation by a reflection sends the C3 generator to its inverse.
-- C3 partitions 27 codes into 3 fixed codes + eight 3-cycles
-- (11 orbits). The complete S3 partitions into seven orbits:
-- 1,2,3,3,6,6,6. Four pairs of C3 orbits are exchanged by odd
-- relabelling, and three C3 orbits remain intact.
--
-- THIS IS THE PRECISE NUMEROLOGY CROSS-POLLINATION:
-- the same C3/S3 parity split governs the VIDEO'S Vandermonde sign,
-- but the 27 objects are endomorphism tables, NOT polynomial roots.
--
-- Original owners: finite ternary S3 conjugacy, seven orbit shapes,
-- and the cubic Vandermonde parity theorem. No geometrical horned
-- group equality, wave equation, 2I, Ibrahim Monster3B or RH follows.
-- New Agda proofs source-written; numerical orbit table separately
-- checked by exhaustive exact Python, Agda kernel PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Foundations.TernaryEndomorphismS3ActionLawsExact as Act
import DASHI.Foundations.PolynomialVandermondeDiscriminantExact as Disc
import DASHI.Foundations.PolynomialVietaRootSymmetryExact as Vieta

Code27 : Set
Code27 = Tower.LevelTwoCode

cycleCode : Code27 → Code27
cycleCode = Perm.conjugateCode Perm.permRotate

reflectionCode : Code27 → Code27
reflectionCode = Perm.conjugateCode Perm.permSwapLowHigh

cycleCodeThreeTimes : (x : Code27) →
  cycleCode (cycleCode (cycleCode x)) ≡ x
cycleCodeThreeTimes x =
  trans
    (cong (cycleCode)
      (sym (Act.conjugateComposition Perm.permRotate Perm.permRotate x)))
    (trans
      (sym (Act.conjugateComposition Perm.permRotate Perm.permRotate2 x))
      (Act.conjugateIdentity x))

reflectionCodeTwice : (x : Code27) →
  reflectionCode (reflectionCode x) ≡ x
reflectionCodeTwice x =
  trans
    (sym (Act.conjugateComposition Perm.permSwapLowHigh Perm.permSwapLowHigh x))
    (Act.conjugateIdentity x)

-- Dihedral relation s r s = r^-1 on the ACTUAL 27 table code
-- action, using the pre-existing S3 multiplication and action laws.
reflectionInvertsCycle : (x : Code27) →
  reflectionCode (cycleCode (reflectionCode x))
    ≡ Perm.conjugateCode Perm.permRotate2 x
reflectionInvertsCycle x =
  trans
    (sym (Act.conjugateComposition Perm.permSwapLowHigh Perm.permRotate
      (reflectionCode x)))
    (trans
      (sym (Act.conjugateComposition
        (S3._∙_ Perm.permSwapLowHigh Perm.permRotate)
        Perm.permSwapLowHigh x))
      refl)

-- Three *distinct* C3-fixed endomorphisms: the commuting
-- permutations 1, r and r². There are no more; exhaustive counting
-- is assigned to the finite executable rather than assumed here.
fixedIdentity :
  cycleCode (Perm.permutationCode Perm.permIdentity)
    ≡ Perm.permutationCode Perm.permIdentity
fixedIdentity = refl

fixedRotate :
  cycleCode (Perm.permutationCode Perm.permRotate)
    ≡ Perm.permutationCode Perm.permRotate
fixedRotate = refl

fixedRotateSquared :
  cycleCode (Perm.permutationCode Perm.permRotate2)
    ≡ Perm.permutationCode Perm.permRotate2
fixedRotateSquared = refl

-- Cubic root discriminant transforms under the SAME abstract S3
-- elements, but on a DIFFERENT carrier (ordered rational roots).
-- We explicitly reuse rather than recreate the sign theorem.
rootParityIsAlternating :
  (p : Perm.TriPermutation) (roots : Vieta.ThreeRoots) →
  Disc.vandermonde (Vieta.permuteRoots p roots) ≡
    Disc.isOdd p (Disc.vandermonde roots)
rootParityIsAlternating = Disc.vandermondeTransformsByParity

rootDiscriminantIsS3Invariant :
  (p : Perm.TriPermutation) (roots : Vieta.ThreeRoots) →
  Disc.discriminant (Vieta.permuteRoots p roots) ≡
    Disc.discriminant roots
rootDiscriminantIsS3Invariant = Disc.discriminantInvariant

-- S3-conjugation of a table and S3-reordering of roots are distinct
-- representations. Their common source is S3, not an identification
-- of root triples with the 27 tables.
