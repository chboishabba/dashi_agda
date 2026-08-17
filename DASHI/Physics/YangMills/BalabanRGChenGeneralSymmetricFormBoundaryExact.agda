module DASHI.Physics.YangMills.BalabanRGChenGeneralSymmetricFormBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Mu-Fa Chen and Feng-Yu Wang,
-- "Cheeger's Inequalities for General Symmetric Forms and Existence Criteria
-- for Spectral Gap", Annals of Probability 28 (2000), 235--257.
-- arXiv: math/9804150 (MSRI Preprint 1998-024).
-- Earlier abstract: Chinese Science Bulletin 43 (1998), 1516--1519.
-- DOI of the 1998 Chinese Science Bulletin abstract: 10.1007/BF02883439.
--
-- The arXiv manuscript explicitly treats general, possibly unbounded,
-- symmetric forms; Theorems 1.1/1.2 improve the bounded-jump Lawler--Sokal
-- route and Theorems 1.4/3.1 give spectral-gap existence criteria using local
-- Dirichlet/Neumann eigenvalues.
--
-- DASHI CONTRIBUTION
--
-- Round59's finite positive neighbour system may converge to an unbounded
-- symmetric Dirichlet form.  In that case it is mathematically wrong to force
-- a bounded Markov-kernel norm merely to use the simplest Lawler--Sokal
-- inequality.  This boundary exposes Chen--Wang as a second theorem regime.
--
-- The bounded specialization is kept in denominator-cleared form:
--
--   h^2 <= 2 M lambda_0.
--
-- The genuinely useful continuum branch is stronger: prove the comparison
-- data / local Dirichlet-Neumann hypotheses for the literal RG form and use
-- the general symmetric-form theorem without requiring finite M.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record ChenWangBoundedCheegerData : Set where
  field
    cheegerConstant : ℚ
    operatorBound : ℚ
    spectralBottom : ℚ
    cheegerNonnegative : 0ℚ ≤ cheegerConstant
    operatorBoundNonnegative : 0ℚ ≤ operatorBound
    chenWangBoundedLowerDenominatorCleared :
      cheegerConstant * cheegerConstant
      ≤ (operatorBound + operatorBound) * spectralBottom
open ChenWangBoundedCheegerData public

data ChenWangSymmetricFormRegime : Set where
  boundedForm generalPossiblyUnboundedForm : ChenWangSymmetricFormRegime

record LiteralRGChenWangRegime : Set₁ where
  field
    regime : ChenWangSymmetricFormRegime
    symmetricDirichletForm : Set
    cheegerComparisonData : Set
    localDirichletNeumannData : Set
open LiteralRGChenWangRegime public

chenWangGeneralSymmetricFormCheegerLevel : ProofLevel
chenWangGeneralSymmetricFormCheegerLevel = standardImported

chenWangLocalEigenvalueSpectralGapCriteriaLevel : ProofLevel
chenWangLocalEigenvalueSpectralGapCriteriaLevel = standardImported

-- Physical leaves.  This route is only preferable if the literal Bałaban RG
-- object is symmetric as a form but naturally unbounded as a generator.  It
-- does not replace the nonreversible Lawler--Sokal branch when symmetry fails.
literalRGSymmetricDirichletFormLevel : ProofLevel
literalRGSymmetricDirichletFormLevel = conditional

literalRGChenWangComparisonWeightsLevel : ProofLevel
literalRGChenWangComparisonWeightsLevel = conditional

cutoffUniformLocalDirichletNeumannGapLevel : ProofLevel
cutoffUniformLocalDirichletNeumannGapLevel = conditional
