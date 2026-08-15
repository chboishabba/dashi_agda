module DASHI.Physics.YangMills.BalabanCMP109SourceNormQuarterReopeningExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- Decouple the Federbush 4/3 estimate from the rational 3x3 matrix carrier.
-- The actual source operator may act on Bishop-real / compact-Lie vectors; for
-- conditioning it suffices to have certified rational majorants in
--
--       ||x|| <= ||y|| + ||R x||,
--       ||R x|| <= (1/4)||x||.
--
-- Pure ordered-rational algebra gives ||x|| <= (4/3)||y||.  Existence is not
-- asserted here: this is a reopening estimate for an already supplied physical
-- solution.  Hence no rational-entry claim about the actual log Jacobian is
-- needed merely to obtain the source conditioning constant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Strict
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

quarter threeQuarters fourThirds : ℚ
quarter = + 1 / 4
threeQuarters = + 3 / 4
fourThirds = + 4 / 3

record SourceNormQuarterEquation : Set where
  field
    solutionNorm sourceNorm residualNorm : ℚ
    solutionNormNonnegative : 0ℚ ≤ solutionNorm
    sourceNormNonnegative : 0ℚ ≤ sourceNorm
    residualNormNonnegative : 0ℚ ≤ residualNorm
    sourceTriangle : solutionNorm ≤ sourceNorm + residualNorm
    quarterResidual : residualNorm ≤ quarter * solutionNorm

open SourceNormQuarterEquation public

quarterGapExact : 1ℚ - quarter ≡ threeQuarters
quarterGapExact = ℚRing.solve []

fourThirdsThreeQuartersExact : fourThirds * threeQuarters ≡ 1ℚ
fourThirdsThreeQuartersExact = ℚRing.solve []

sourceNormQuarterGap :
  ∀ dataSet → threeQuarters * solutionNorm dataSet ≤ sourceNorm dataSet
sourceNormQuarterGap dataSet =
  let
    replaced :
      solutionNorm dataSet
      ≤ sourceNorm dataSet + quarter * solutionNorm dataSet
    replaced = ℚP.≤-trans
      (sourceTriangle dataSet)
      (ℚP.+-monoʳ-≤ (sourceNorm dataSet) (quarterResidual dataSet))
    gapRaw = Strict.reopeningGapBound
      (solutionNorm dataSet) (sourceNorm dataSet) quarter replaced
  in
  subst
    (λ lower → lower ≤ sourceNorm dataSet)
    (cong (_* solutionNorm dataSet) quarterGapExact)
    gapRaw

sourceNormQuarterReopeningFourThirds :
  ∀ dataSet → solutionNorm dataSet ≤ fourThirds * sourceNorm dataSet
sourceNormQuarterReopeningFourThirds dataSet =
  let
    scaled = Norm.scaleNonnegative fourThirds
      (ℚP.nonNegative⁻¹ fourThirds)
      (sourceNormQuarterGap dataSet)
    leftExact :
      fourThirds * (threeQuarters * solutionNorm dataSet)
      ≡ solutionNorm dataSet
    leftExact =
      trans
        (sym (ℚP.*-assoc fourThirds threeQuarters (solutionNorm dataSet)))
        (trans
          (cong (_* solutionNorm dataSet) fourThirdsThreeQuartersExact)
          (ℚP.*-identityˡ (solutionNorm dataSet)))
  in
  subst
    (λ lower → lower ≤ fourThirds * sourceNorm dataSet)
    leftExact scaled

sourceNormHomogeneousNormZero :
  ∀ dataSet → sourceNorm dataSet ≡ 0ℚ → solutionNorm dataSet ≡ 0ℚ
sourceNormHomogeneousNormZero dataSet sourceZero =
  let
    upper : solutionNorm dataSet ≤ 0ℚ
    upper = subst
      (λ upper → solutionNorm dataSet ≤ upper)
      (trans
        (cong (fourThirds *_) sourceZero)
        (ℚRing.solve []))
      (sourceNormQuarterReopeningFourThirds dataSet)
  in
  ℚP.≤-antisym upper (solutionNormNonnegative dataSet)

cmp109SourceNormQuarterReopeningLevel : ProofLevel
cmp109SourceNormQuarterReopeningLevel = machineChecked

cmp109SourceNormQuarterHomogeneousNormLevel : ProofLevel
cmp109SourceNormQuarterHomogeneousNormLevel = machineChecked
