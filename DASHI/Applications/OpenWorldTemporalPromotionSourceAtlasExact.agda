module DASHI.Applications.OpenWorldTemporalPromotionSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- OPEN-WORLD TEMPORAL / PROMOTION SOURCE ATLAS
--
-- Sources pay only bounded conceptual/evaluation coordinates.  They do not
-- identify any RF emitter, validate any vendor implementation, or import their
-- mathematical results as Agda proofs.
------------------------------------------------------------------------

boultEtAl2019 : Source.AttributedSource
boultEtAl2019 =
  Source.mkDOISource
    "Terrance E. Boult; Steve Cruz; Abhijit R. Dhamija; Manuel Gunther; James Henrydoss; Walter J. Scheirer"
    "Learning and the Unknown: Surveying Steps toward Open World Recognition"
    "Proceedings of the AAAI Conference on Artificial Intelligence 33(01), 9801-9807"
    "2019"
    "10.1609/aaai.v33i01.33019801"
    "https://doi.org/10.1609/aaai.v33i01.33019801"
    Source.academicArticleSource
    "source for the boundary that uncertainty/rejection is not identical to unknownness and that unknown handling requires more than a generic low-confidence rule"
    Source.publicAttribution

kimEtAl2025 : Source.AttributedSource
kimEtAl2025 =
  Source.mkDOISource
    "Gyuhak Kim; Changnan Xiao; Tatsuya Konishi; Zixuan Ke; Bing Liu"
    "Open-world continual learning: Unifying novelty detection and continual learning"
    "Artificial Intelligence 338, 104237"
    "2025"
    "10.1016/j.artint.2024.104237"
    "https://doi.org/10.1016/j.artint.2024.104237"
    Source.academicArticleSource
    "source for the explicit coupling between novelty/OOD handling and continual/class-incremental learning in open-world continual learning; citation does not itself prove a DASHI theorem"
    Source.publicAttribution

cruzEtAl2025 : Source.AttributedSource
cruzEtAl2025 =
  Source.mkDOISource
    "Steve Cruz; Katarina Doctor; Christopher Funk; Walter Scheirer"
    "Open issues in open world learning"
    "AI Magazine 46(2)"
    "2025"
    "10.1002/aaai.70001"
    "https://doi.org/10.1002/aaai.70001"
    Source.academicArticleSource
    "source for novelty detection, characterization, incremental learning, and evaluation-discipline concerns including misleading metrics and test-set tuning in open-world learning"
    Source.publicAttribution

openWorldTemporalPromotionSources : List Source.AttributedSource
openWorldTemporalPromotionSources =
  boultEtAl2019 ∷ kimEtAl2025 ∷ cruzEtAl2025 ∷ []

openWorldTemporalPromotionSourceAtlas : Source.AttributedSourceAtlas
openWorldTemporalPromotionSourceAtlas =
  Source.mkSourceAtlas
    "open-world temporal knowledge and promotion discipline"
    "DASHI.Applications.OpenWorldTemporalPromotionSourceAtlasExact"
    openWorldTemporalPromotionSources
    "bounded source atlas for uncertainty-vs-unknown, novelty plus continual learning, temporal knowledge growth, and held-out evaluation discipline; sources do not identify DroneShield emitters or create operational authority"

openWorldTemporalPromotionSourceAtlasCreatesAuthority : Bool
openWorldTemporalPromotionSourceAtlasCreatesAuthority =
  Source.atlasCreatesAuthority openWorldTemporalPromotionSourceAtlas

openWorldTemporalPromotionSourceAtlasCreatesAuthorityIsFalse :
  openWorldTemporalPromotionSourceAtlasCreatesAuthority ≡ false
openWorldTemporalPromotionSourceAtlasCreatesAuthorityIsFalse =
  Source.atlasCreatesAuthorityIsFalse openWorldTemporalPromotionSourceAtlas

record OpenWorldTemporalPromotionAttributionBoundary : Set where
  constructor openWorldTemporalPromotionAttributionBoundary
  field
    literatureAnalogyEqualsVendorValidation : Bool
    literatureAnalogyEqualsVendorValidationIsFalse :
      literatureAnalogyEqualsVendorValidation ≡ false
    laterKnowledgeCreatesEarlierKnowledge : Bool
    laterKnowledgeCreatesEarlierKnowledgeIsFalse :
      laterKnowledgeCreatesEarlierKnowledge ≡ false
    citationCreatesIdentityAuthority : Bool
    citationCreatesIdentityAuthorityIsFalse :
      citationCreatesIdentityAuthority ≡ false
    citedSourceTheoremEqualsImportedDASHIProof : Bool
    citedSourceTheoremEqualsImportedDASHIProofIsFalse :
      citedSourceTheoremEqualsImportedDASHIProof ≡ false

canonicalOpenWorldTemporalPromotionAttributionBoundary :
  OpenWorldTemporalPromotionAttributionBoundary
canonicalOpenWorldTemporalPromotionAttributionBoundary =
  openWorldTemporalPromotionAttributionBoundary
    false refl
    false refl
    false refl
    false refl
