module DASHI.Foundations.PolynomialVandermondeOrbitParityIntertwinerExact where

------------------------------------------------------------------------
-- ACTUAL COMMON S3 -> C2 SIGN CHARACTER BETWEEN DIFFERENT OBJECTS.
-- Root action: the alternating Vandermonde (ordered rational roots).
-- Endomorphism action: S3 conjugation of 27 ternary maps; its
-- eleven C3-orbits carry an S3 action FACTORING THROUGH C2.
-- Common source: genuine permutation parity character, not a
-- root/endomorphism bijection, Monster character, SU2 spin, or
-- wild-exterior identification.
--
-- SOURCE-WRITTEN, exact full 162-case C3-quotient action table,
-- Agda kernel pending. Classical permutation-sign representation
-- predates this owner; earlier conjugacy and Vandermonde proofs reused.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; -_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Base369 as Base
import DASHI.Foundations.StageSymmetryCarrierTowerExact as Stage
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact as Cyclic
import DASHI.Foundations.PolynomialC3S3TwentySevenOrbitQuotientExact as Q
import DASHI.Foundations.PolynomialVandermondeDiscriminantExact as Disc
import DASHI.Foundations.PolynomialVietaRootSymmetryExact as Vieta

permutationParity : Shape.TriPermutation → Stage.C2
permutationParity Shape.permIdentity = Stage.direct
permutationParity Shape.permRotate = Stage.direct
permutationParity Shape.permRotate2 = Stage.direct
permutationParity Shape.permSwapLowMid = Stage.inverse
permutationParity Shape.permSwapLowHigh = Stage.inverse
permutationParity Shape.permSwapMidHigh = Stage.inverse

parityHomomorphism :
  (p q : Shape.TriPermutation) →
  permutationParity (S3._∙_ p q) ≡
  Cyclic._+₂_ (permutationParity p) (permutationParity q)
parityHomomorphism Shape.permIdentity Shape.permIdentity = refl
parityHomomorphism Shape.permIdentity Shape.permRotate = refl
parityHomomorphism Shape.permIdentity Shape.permRotate2 = refl
parityHomomorphism Shape.permIdentity Shape.permSwapLowMid = refl
parityHomomorphism Shape.permIdentity Shape.permSwapLowHigh = refl
parityHomomorphism Shape.permIdentity Shape.permSwapMidHigh = refl
parityHomomorphism Shape.permRotate Shape.permIdentity = refl
parityHomomorphism Shape.permRotate Shape.permRotate = refl
parityHomomorphism Shape.permRotate Shape.permRotate2 = refl
parityHomomorphism Shape.permRotate Shape.permSwapLowMid = refl
parityHomomorphism Shape.permRotate Shape.permSwapLowHigh = refl
parityHomomorphism Shape.permRotate Shape.permSwapMidHigh = refl
parityHomomorphism Shape.permRotate2 Shape.permIdentity = refl
parityHomomorphism Shape.permRotate2 Shape.permRotate = refl
parityHomomorphism Shape.permRotate2 Shape.permRotate2 = refl
parityHomomorphism Shape.permRotate2 Shape.permSwapLowMid = refl
parityHomomorphism Shape.permRotate2 Shape.permSwapLowHigh = refl
parityHomomorphism Shape.permRotate2 Shape.permSwapMidHigh = refl
parityHomomorphism Shape.permSwapLowMid Shape.permIdentity = refl
parityHomomorphism Shape.permSwapLowMid Shape.permRotate = refl
parityHomomorphism Shape.permSwapLowMid Shape.permRotate2 = refl
parityHomomorphism Shape.permSwapLowMid Shape.permSwapLowMid = refl
parityHomomorphism Shape.permSwapLowMid Shape.permSwapLowHigh = refl
parityHomomorphism Shape.permSwapLowMid Shape.permSwapMidHigh = refl
parityHomomorphism Shape.permSwapLowHigh Shape.permIdentity = refl
parityHomomorphism Shape.permSwapLowHigh Shape.permRotate = refl
parityHomomorphism Shape.permSwapLowHigh Shape.permRotate2 = refl
parityHomomorphism Shape.permSwapLowHigh Shape.permSwapLowMid = refl
parityHomomorphism Shape.permSwapLowHigh Shape.permSwapLowHigh = refl
parityHomomorphism Shape.permSwapLowHigh Shape.permSwapMidHigh = refl
parityHomomorphism Shape.permSwapMidHigh Shape.permIdentity = refl
parityHomomorphism Shape.permSwapMidHigh Shape.permRotate = refl
parityHomomorphism Shape.permSwapMidHigh Shape.permRotate2 = refl
parityHomomorphism Shape.permSwapMidHigh Shape.permSwapLowMid = refl
parityHomomorphism Shape.permSwapMidHigh Shape.permSwapLowHigh = refl
parityHomomorphism Shape.permSwapMidHigh Shape.permSwapMidHigh = refl

actSignOnEleven : Stage.C2 → Q.Orbit11 → Q.Orbit11
actSignOnEleven Stage.direct o = o
actSignOnEleven Stage.inverse o = Q.reflectionOn11 o

signActionComposition :
  (p q : Stage.C2) (o : Q.Orbit11) →
  actSignOnEleven (Cyclic._+₂_ p q) o ≡
  actSignOnEleven p (actSignOnEleven q o)
signActionComposition Stage.direct Stage.direct o = refl
signActionComposition Stage.direct Stage.inverse o = refl
signActionComposition Stage.inverse Stage.direct o = refl
signActionComposition Stage.inverse Stage.inverse o =
  Q.reflection11Involutive o

fullS3ActionOnEleven : Shape.TriPermutation → Q.Orbit11 → Q.Orbit11
fullS3ActionOnEleven p o = actSignOnEleven (permutationParity p) o

fullS3ActionOnElevenComposition :
  (p q : Shape.TriPermutation) (o : Q.Orbit11) →
  fullS3ActionOnEleven (S3._∙_ p q) o ≡
  fullS3ActionOnEleven p (fullS3ActionOnEleven q o)
fullS3ActionOnElevenComposition p q o
  rewrite parityHomomorphism p q =
  signActionComposition (permutationParity p) (permutationParity q) o

-- All 162 cases reuse the pre-existing 27-conjugation operation and
-- eleven-orbit classifier. This is EXACT table verification, not
-- an assumption from the shared count 27.
classifyConjugationByParity :
  (p : Shape.TriPermutation) (x : Q.Code27) →
  Q.classify11 (Shape.conjugateCode p x) ≡
    fullS3ActionOnEleven p (Q.classify11 x)
classifyConjugationByParity Shape.permIdentity (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permIdentity (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permRotate2 (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowMid (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapLowHigh (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
classifyConjugationByParity Shape.permSwapMidHigh (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

signedRational : Stage.C2 → ℚ → ℚ
signedRational Stage.direct x = x
signedRational Stage.inverse x = - x

rationalSignFactors :
  (p : Shape.TriPermutation) (x : ℚ) →
  Disc.isOdd p x ≡ signedRational (permutationParity p) x
rationalSignFactors Shape.permIdentity x = refl
rationalSignFactors Shape.permRotate x = refl
rationalSignFactors Shape.permRotate2 x = refl
rationalSignFactors Shape.permSwapLowMid x = refl
rationalSignFactors Shape.permSwapLowHigh x = refl
rationalSignFactors Shape.permSwapMidHigh x = refl

-- Genuine Vandermonde sign intertwining through the SAME parity
-- homomorphism that controls S3 on eleven ternary endomorphism orbits.
vandermondeIntertwinesSign :
  (p : Shape.TriPermutation) (roots : Vieta.ThreeRoots) →
  Disc.vandermonde (Vieta.permuteRoots p roots) ≡
  signedRational (permutationParity p) (Disc.vandermonde roots)
vandermondeIntertwinesSign p roots =
  trans (Disc.vandermondeTransformsByParity p roots)
    (rationalSignFactors p (Disc.vandermonde roots))

discriminantStillS3Invariant :
  (p : Shape.TriPermutation) (roots : Vieta.ThreeRoots) →
  Disc.discriminant (Vieta.permuteRoots p roots) ≡
  Disc.discriminant roots
discriminantStillS3Invariant = Disc.discriminantInvariant

-- The two actions share only the sign quotient S3 -> C2.
-- Their state spaces and observable coefficient rings are different.
