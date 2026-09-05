module DASHI.Analysis.NonArchimedeanSpectralTowerSourceRepairBidiExact where

------------------------------------------------------------------------
-- SPECTRAL-TOWER SOURCE REPAIR
--
-- `CollatzRelMatrix.spectral_tower_one_step` is currently theorem-shaped only
-- by name/comment: its formal conclusion is literally `True`.
--
-- However `CoveringFactorization.det_collatzDirMatrix_factorization` is a real
-- theorem on the concrete matrices:
--
--   det(I - u D_n)
--     = det(I - u D_(n-1)) * det(I - u S_n).
--
-- Thus the source owns the determinant-factorization producer needed for the
-- recursive spectral story.  The literal spectrum-union theorem should be
-- derived from that factorization (or directly from the already-owned block
-- similarity) using the existing finite-dimensional spectral machinery.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

record SourceTowerStatus : Set where
  constructor sourceTowerStatus
  field
    hadamardBlockDiagonalizationOwned : Bool
    weightedBlockEqualsPreviousLevelOwned : Bool
    determinantFactorizationOwned : Bool
    theoremNamedSpectralTowerHasSpectrumUnionConclusion : Bool
    theoremNamedSpectralTowerConclusionIsTrueOnly : Bool
    literalSpectrumUnionOwnedInLocatedSource : Bool

canonicalSourceTowerStatus : SourceTowerStatus
canonicalSourceTowerStatus =
  sourceTowerStatus true true true false true false


data TowerObligation : Set where
  transportBlockSimilarityToSpectrum : TowerObligation
  transportDetFactorizationToSpectralRoots : TowerObligation
  recurseFiniteTower : TowerObligation
  rebuildHadamardBlockDiagonalization : TowerObligation
  rebuildDeterminantFactorization : TowerObligation
  acceptTruePlaceholderAsSpectrumTheorem : TowerObligation


data TowerDisposition : Set where
  live : TowerDisposition
  alternative : TowerDisposition
  downstream : TowerDisposition
  pruned : TowerDisposition
  forbiddenShortcut : TowerDisposition

towerDisposition : TowerObligation → TowerDisposition
towerDisposition transportBlockSimilarityToSpectrum = live
towerDisposition transportDetFactorizationToSpectralRoots = alternative
towerDisposition recurseFiniteTower = downstream
towerDisposition rebuildHadamardBlockDiagonalization = pruned
towerDisposition rebuildDeterminantFactorization = pruned
towerDisposition acceptTruePlaceholderAsSpectrumTheorem = forbiddenShortcut

highestAlphaTowerPath : List TowerObligation
highestAlphaTowerPath =
  transportBlockSimilarityToSpectrum ∷
  recurseFiniteTower ∷
  []

record TowerPromotionFirewall : Set where
  constructor towerPromotionFirewall
  field
    theoremCommentCountsAsTheoremType : Bool
    theoremNameCountsAsTheoremType : Bool
    truePlaceholderCountsAsSpectralUnion : Bool
    determinantFactorizationCountsAsNoInformation : Bool

canonicalTowerPromotionFirewall : TowerPromotionFirewall
canonicalTowerPromotionFirewall =
  towerPromotionFirewall false false false false

placeholderDoesNotOwnSpectrumUnion :
  SourceTowerStatus.literalSpectrumUnionOwnedInLocatedSource
    canonicalSourceTowerStatus
  ≡ false
placeholderDoesNotOwnSpectrumUnion = refl

determinantProducerAlreadyOwned :
  SourceTowerStatus.determinantFactorizationOwned canonicalSourceTowerStatus
  ≡ true
determinantProducerAlreadyOwned = refl
