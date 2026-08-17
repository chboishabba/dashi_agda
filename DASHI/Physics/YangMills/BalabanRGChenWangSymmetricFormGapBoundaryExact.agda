module DASHI.Physics.YangMills.BalabanRGChenWangSymmetricFormGapBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Mu-Fa Chen and Feng-Yu Wang,
-- "Cheeger's Inequalities for General Symmetric Forms and Existence Criteria
-- for Spectral Gap", The Annals of Probability 28 (2000), 235--257.
-- DOI: 10.1214/aop/1019160118.
-- Preprint: arXiv:math/9804150.
--
-- Earlier announcement:
-- Mu-Fa Chen and Feng-Yu Wang, Chinese Science Bulletin 43 (1998),
-- 1516--1519. DOI: 10.1007/BF02883439.
--
-- SOURCE ROLE
--
-- Chen--Wang establish Cheeger inequalities for general, possibly unbounded,
-- symmetric forms and spectral-gap existence criteria using local Dirichlet /
-- Neumann eigenvalues.  Their framework improves/extends the bounded jump-
-- process estimates of Lawler--Sokal in the symmetric-form setting.
--
-- DASHI BOUNDARY
--
-- This is an ALTERNATIVE to the Lawler--Sokal route, not an additional theorem
-- that the Clay lane must prove.  It is available only if the literal Bałaban
-- RG generator naturally produces a symmetric (possibly unbounded) form with
-- the source hypotheses required by Chen--Wang.  The physical programme should
-- choose the shortest theorem family after the literal RG object is known.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

-- A tag only: it prevents the frontier root from silently requiring both a
-- bounded Markov-kernel route and an unbounded symmetric-form route.
data RGSpectralRoute : Set where
  lawlerSokalRoute chenWangSymmetricFormRoute : RGSpectralRoute

chenWangGeneralSymmetricFormCheegerLevel : ProofLevel
chenWangGeneralSymmetricFormCheegerLevel = standardImported

chenWangLocalDirichletNeumannGapCriteriaLevel : ProofLevel
chenWangLocalDirichletNeumannGapCriteriaLevel = standardImported

-- New Yang--Mills work if this route is selected: identify the SAME literal
-- Bałaban RG object with the symmetric form and prove its quantitative
-- isoperimetric/local-eigenvalue hypotheses uniformly in cutoff and volume.
literalBalabanSymmetricFormIdentificationLevel : ProofLevel
literalBalabanSymmetricFormIdentificationLevel = conditional

cutoffUniformChenWangHypothesesLevel : ProofLevel
cutoffUniformChenWangHypothesesLevel = conditional

-- Only one spectral route is needed in the shortest proof.
multipleSpectralRoutesRequiredLevel : ProofLevel
multipleSpectralRoutesRequiredLevel = refuted
