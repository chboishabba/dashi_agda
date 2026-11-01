module DASHI.Applications.CounterUASNoveltyPromotionSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- NOVELTY PROMOTION / CONTAMINATION SOURCE ATLAS
--
-- These papers support general open-world/continual-learning boundaries around
-- scarce labels, open-set noise, label-space shift, and noisy-memory effects.
-- They do not identify an RF emitter, validate DroneShield, or create legal or
-- operational authority.
------------------------------------------------------------------------

nieEtAl2025 : Source.AttributedSource
nieEtAl2025 =
  Source.mkDOISource
    "Hongyi Nie; Shiqi Fan; Yang Liu; Quanming Yao; Zhen Wang"
    "Using samples with label noise for robust continual learning"
    "Neural Networks 188, 107422"
    "2025"
    "10.1016/j.neunet.2025.107422"
    "https://doi.org/10.1016/j.neunet.2025.107422"
    Source.academicArticleSource
    "source for the boundary that continual/open-world label-space shift can invalidate naive label-correction assumptions and can propagate new label noise when samples are assigned to the wrong label space"
    Source.publicAttribution

liEtAl2025PAA : Source.AttributedSource
liEtAl2025PAA =
  Source.mkDOISource
    "Shao-Yuan Li; Yu-Xiang Zheng; Sheng-Jun Huang; Songcan Chen; Kangkan Wang"
    "Prototypes as Anchors: Tackling Unseen Noise for online continual learning"
    "Neural Networks 190, 107634"
    "2025"
    "10.1016/j.neunet.2025.107634"
    "https://doi.org/10.1016/j.neunet.2025.107634"
    Source.academicArticleSource
    "source for distinguishing closed-set from open-set noise in online class-incremental learning, and for the need to detect unseen-class contamination rather than treating every noisy sample as belonging to the current known label space"
    Source.publicAttribution

liEtAlKDD2025 : Source.AttributedSource
liEtAlKDD2025 =
  Source.mkDOISource
    "Yujie Li; Xiangkun Wang; Xin Yang; Marcello Bonsangue; Junbo Zhang; Tianrui Li"
    "Improving Open-world Continual Learning under the Constraints of Scarce Labeled Data"
    "Proceedings of the 31st ACM SIGKDD Conference on Knowledge Discovery and Data Mining V.2, 1647-1658"
    "2025"
    "10.1145/3711896.3737004"
    "https://doi.org/10.1145/3711896.3737004"
    Source.academicArticleSource
    "source for open-world continual learning with scarce labelled data and the distinction between detecting open samples and later updating unknowns to knowns once labels become available"
    Source.publicAttribution

noveltyPromotionSources : List Source.AttributedSource
noveltyPromotionSources =
  nieEtAl2025 ∷ liEtAl2025PAA ∷ liEtAlKDD2025 ∷ []

noveltyPromotionSourceAtlas : Source.AttributedSourceAtlas
noveltyPromotionSourceAtlas =
  Source.mkSourceAtlas
    "novelty promotion and contamination discipline"
    "DASHI.Applications.CounterUASNoveltyPromotionSourceAtlasExact"
    noveltyPromotionSources
    "general academic support for label-space shift, open-set noise, scarce-label open-world learning, and unknown-to-known updates; no source is treated as product-specific validation or emitter identity authority"

noveltyPromotionSourceAtlasCreatesAuthority : Bool
noveltyPromotionSourceAtlasCreatesAuthority =
  Source.atlasCreatesAuthority noveltyPromotionSourceAtlas

noveltyPromotionSourceAtlasCreatesAuthorityIsFalse :
  noveltyPromotionSourceAtlasCreatesAuthority ≡ false
noveltyPromotionSourceAtlasCreatesAuthorityIsFalse =
  Source.atlasCreatesAuthorityIsFalse noveltyPromotionSourceAtlas

nieSnowballReceipt : Snowball.SourceRoleSnowballReceipt nieEtAl2025
nieSnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt nieEtAl2025

paaSnowballReceipt : Snowball.SourceRoleSnowballReceipt liEtAl2025PAA
paaSnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt liEtAl2025PAA

ofclSnowballReceipt : Snowball.SourceRoleSnowballReceipt liEtAlKDD2025
ofclSnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt liEtAlKDD2025

record NoveltyPromotionAttributionBoundary : Set where
  constructor noveltyPromotionAttributionBoundary
  field
    academicNoisePaperIdentifiesSpecificEmitter : Bool
    academicNoisePaperIdentifiesSpecificEmitterIsFalse :
      academicNoisePaperIdentifiesSpecificEmitter ≡ false
    generalContinualLearningPaperValidatesVendorImplementation : Bool
    generalContinualLearningPaperValidatesVendorImplementationIsFalse :
      generalContinualLearningPaperValidatesVendorImplementation ≡ false
    sourceAgreementCreatesIndependentGenealogy : Bool
    sourceAgreementCreatesIndependentGenealogyIsFalse :
      sourceAgreementCreatesIndependentGenealogy ≡ false
    citationCreatesPromotionEligibility : Bool
    citationCreatesPromotionEligibilityIsFalse :
      citationCreatesPromotionEligibility ≡ false

canonicalNoveltyPromotionAttributionBoundary :
  NoveltyPromotionAttributionBoundary
canonicalNoveltyPromotionAttributionBoundary =
  noveltyPromotionAttributionBoundary false refl false refl false refl false refl
