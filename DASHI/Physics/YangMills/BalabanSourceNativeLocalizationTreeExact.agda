module DASHI.Physics.YangMills.BalabanSourceNativeLocalizationTreeExact where

------------------------------------------------------------------------
-- ROUND76: SOURCE d_j(X) IS THE REPOSITORY TREE COORDINATE BY CONSTRUCTION
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Immediately before (0.24)--(0.27), d_j(X) is defined by the shortest tree
-- graph contained in X which meets every M-cube, with length divided by M.
-- `BalabanCMP109LocalizationTreeSizeDictionaryExact` already imports that
-- source definition.  The remaining `repository localization domain`
-- identification disappears if the strong state uses this source domain as
-- its polymer/localization carrier rather than copying it into a second type.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109LocalizationTreeSizeDictionaryExact as Tree

record SourceNativeLocalizationCarrier : Set₁ where
  field
    Scale Domain : Set
    sourceGeometry : Tree.CMP109LocalizationTreeGeometry Scale Domain

open SourceNativeLocalizationCarrier public

repositoryTreeSize :
  (carrier : SourceNativeLocalizationCarrier) →
  Scale carrier → Domain carrier → ℚ
repositoryTreeSize carrier =
  Tree.normalizedShortestCubeTreeLength (sourceGeometry carrier)

sourceNativeExactTreeDictionary :
  (carrier : SourceNativeLocalizationCarrier) →
  Tree.ExactRepositoryTreeDictionary (sourceGeometry carrier)
sourceNativeExactTreeDictionary carrier = record
  { Tree.ExactRepositoryTreeDictionary.repositoryTreeSize =
      repositoryTreeSize carrier
  ; Tree.ExactRepositoryTreeDictionary.repositoryTreeUsesSameCubeEdgeMinimum =
      λ scale domain → refl
  }

sourceTreeSizeEqualsStrongStateTreeSize :
  (carrier : SourceNativeLocalizationCarrier) →
  ∀ scale domain →
  Tree.sourceLinearSize (sourceGeometry carrier) scale domain
  ≡ repositoryTreeSize carrier scale domain
sourceTreeSizeEqualsStrongStateTreeSize carrier =
  Tree.sourceSizeEqualsRepositoryTreeSize
    (sourceNativeExactTreeDictionary carrier)

sourceNativeLocalizationTreeDictionaryLevel : ProofLevel
sourceNativeLocalizationTreeDictionaryLevel = machineChecked

-- No physical estimate is hidden here.  The source-native choice removes only
-- a duplicated carrier/normalization seam.  The actual activity magnitudes and
-- their strong-norm summability remain part of the unified one-step theorem.
