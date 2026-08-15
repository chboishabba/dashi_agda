module DASHI.Physics.YangMills.BalabanCMP109LocalizationTreeSizeDictionaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DIRECT LOCATOR
--
-- Introduction, immediately before equations (0.24)--(0.27), pp. 257--258.
-- A localization domain X is a connected finite union of M-cubes.  Bałaban
-- considers tree graphs contained in X which intersect every cube of X; d_j(X)
-- is the length of a shortest such graph divided by M.  He explicitly notes an
-- equivalent definition using shortest tree graphs made from edges of cubes in
-- X.  Thus after rescaling M-cubes to unit cubes, d_j(X) is already a normalized
-- tree-size quantity, not an unrelated Euclidean diameter.
--
-- DASHI CONTRIBUTION
--
-- Expose that source geometry as the exact dictionary needed by the CMP119/
-- CMP122 R-decay lane.  If a repository rooted-polymer carrier uses the same
-- connected M-cube family and its treeSize counts the normalized edge length of
-- a shortest spanning cube-tree, then no metric-loss constant is needed:
--
--                         d_j(X) = treeSize(X).
--
-- A weaker comparison record is also provided for representations which count
-- a different but dominating tree witness.  This keeps any normalization loss
-- explicit instead of silently spending the CMP119 arbitrary decay reserve.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP109LocalizationTreeGeometry
    (Scale Domain : Set) : Set₁ where
  field
    sourceLinearSize : Scale → Domain → ℚ
    normalizedShortestCubeTreeLength : Scale → Domain → ℚ

    -- Literal source definition: shortest graph length / M after the M-cube
    -- lattice is rescaled to unit cubes.
    sourceLinearSizeIsNormalizedShortestTree : ∀ scale domain →
      sourceLinearSize scale domain
      ≡ normalizedShortestCubeTreeLength scale domain

open CMP109LocalizationTreeGeometry public

record ExactRepositoryTreeDictionary
    {Scale Domain : Set}
    (source : CMP109LocalizationTreeGeometry Scale Domain) : Set₁ where
  field
    repositoryTreeSize : Scale → Domain → ℚ

    repositoryTreeUsesSameCubeEdgeMinimum : ∀ scale domain →
      repositoryTreeSize scale domain
      ≡ normalizedShortestCubeTreeLength source scale domain

open ExactRepositoryTreeDictionary public

sourceSizeEqualsRepositoryTreeSize :
  ∀ {Scale Domain}
    {source : CMP109LocalizationTreeGeometry Scale Domain}
    (dictionary : ExactRepositoryTreeDictionary source)
    scale domain →
  sourceLinearSize source scale domain
  ≡ repositoryTreeSize dictionary scale domain
sourceSizeEqualsRepositoryTreeSize {source = source} dictionary scale domain =
  trans
    (sourceLinearSizeIsNormalizedShortestTree source scale domain)
    (sym (repositoryTreeUsesSameCubeEdgeMinimum dictionary scale domain))
  where
  open import Relation.Binary.PropositionalEquality using (sym; trans)

record DominatingRepositoryTreeDictionary
    {Scale Domain : Set}
    (source : CMP109LocalizationTreeGeometry Scale Domain) : Set₁ where
  field
    repositoryTreeSize : Scale → Domain → ℚ
    sourceTreeDominatesRepositoryTree : ∀ scale domain →
      repositoryTreeSize scale domain
      ≤ normalizedShortestCubeTreeLength source scale domain

open DominatingRepositoryTreeDictionary public

repositoryTreeBelowSourceSize :
  ∀ {Scale Domain}
    {source : CMP109LocalizationTreeGeometry Scale Domain}
    (dictionary : DominatingRepositoryTreeDictionary source)
    scale domain →
  repositoryTreeSize dictionary scale domain
  ≤ sourceLinearSize source scale domain
repositoryTreeBelowSourceSize {source = source} dictionary scale domain =
  subst
    (λ upper → repositoryTreeSize dictionary scale domain ≤ upper)
    (sym (sourceLinearSizeIsNormalizedShortestTree source scale domain))
    (sourceTreeDominatesRepositoryTree dictionary scale domain)
  where
  open import Relation.Binary.PropositionalEquality using (sym)

cmp109LocalizationDomainTreeDefinitionLevel : ProofLevel
cmp109LocalizationDomainTreeDefinitionLevel = standardImported

cmp109ExactTreeMetricTransportLevel : ProofLevel
cmp109ExactTreeMetricTransportLevel = machineChecked

cmp109DominatingTreeMetricTransportLevel : ProofLevel
cmp109DominatingTreeMetricTransportLevel = machineChecked

-- Physical representation seam: instantiate the repository R-polymer support
-- as precisely the same connected M-cube localization domain (or prove the
-- weaker domination above).  The primary source no longer leaves d_j opaque.
cmp109RepositoryLocalizationDomainIdentificationLevel : ProofLevel
cmp109RepositoryLocalizationDomainIdentificationLevel = conditional
