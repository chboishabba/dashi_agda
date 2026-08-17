module DASHI.Physics.YangMills.BalabanRGChenGeneralSymmetricFormBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Mu-Fa Chen and Feng-Yu Wang,
-- "Cheeger's Inequalities for General Symmetric Forms and Existence Criteria
-- for Spectral Gap", Annals of Probability 28 (2000), 235--257.
-- arXiv: math/9804150 (MSRI Preprint 1998-024).
--
-- Earlier announcement:
-- Mu-Fa Chen and Feng-Yu Wang,
-- "Cheeger's Inequalities for General Symmetric Forms and Existence Criteria
-- for Spectral Gap", Chinese Science Bulletin 43 (1998), 1516--1518.
-- DOI: 10.1007/BF02883439.
--
-- SOURCE-SCOPE NOTE
--
-- The 1998 bulletin item is the short announcement.  It explicitly notes that
-- the reversible-Markov-process extension is not reported there.  The full
-- general-symmetric-form and reversible-process proof content used by this
-- boundary is therefore attributed to the 2000 Annals of Probability paper,
-- with the 1998 DOI retained only as provenance for the announcement.
--
-- The full paper treats general, possibly unbounded, symmetric forms;
-- Theorems 1.1/1.2 sharpen the bounded-jump Cheeger route and the local
-- Dirichlet/Neumann criteria give a separate existence route for spectral gap.
--
-- DASHI CONTRIBUTION
--
-- Round59's finite positive neighbour system may converge to an unbounded
-- symmetric Dirichlet form.  In that case it is mathematically wrong to force
-- a bounded Markov-kernel norm merely to use the simplest Lawler--Sokal
-- inequality.  This boundary exposes Chen--Wang as a second theorem regime.
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

literalRGSymmetricDirichletFormLevel : ProofLevel
literalRGSymmetricDirichletFormLevel = conditional

literalRGChenWangComparisonWeightsLevel : ProofLevel
literalRGChenWangComparisonWeightsLevel = conditional

cutoffUniformLocalDirichletNeumannGapLevel : ProofLevel
cutoffUniformLocalDirichletNeumannGapLevel = conditional
