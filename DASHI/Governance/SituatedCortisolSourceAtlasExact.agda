module DASHI.Governance.SituatedCortisolSourceAtlasExact where

-- Correct source ownership for person-conditioned endocrine models.
-- These sources motivate variables and interpretation boundaries.
-- None supplies validated person-specific quantitative parameters here.
-- HPA cascade and body-supervoxel formal owners already exist in DASHI.

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Attr

dickersonKemeny2004 : Attr.AttributedSource
dickersonKemeny2004 = Attr.mkDOISource
  "Sally S. Dickerson and Margaret E. Kemeny"
  "Acute stressors and cortisol responses: A theoretical integration and synthesis of laboratory research"
  "Psychological Bulletin 130(3), 355-391"
  "2004"
  "10.1037/0033-2909.130.3.355"
  "https://pubmed.ncbi.nlm.nih.gov/15122924/"
  Attr.academicArticleSource
  "Meta-analysis of conditions eliciting HPA responses; social evaluation and uncontrollability are contextual variables, not a deterministic personal cortisol function"
  Attr.publicAttribution

khouryEnlowPlamondonLyonsRuth2019 : Attr.AttributedSource
khouryEnlowPlamondonLyonsRuth2019 = Attr.mkDOISource
  "Jennifer E. Khoury, Michelle Bosquet Enlow, Andre Plamondon, and Karlen Lyons-Ruth"
  "The association between adversity and hair cortisol levels in humans: A meta-analysis"
  "Psychoneuroendocrinology 103, 104-117"
  "2019"
  "10.1016/j.psyneuen.2019.01.009"
  "https://pmc.ncbi.nlm.nih.gov/articles/PMC6450779/"
  Attr.academicArticleSource
  "Human adversity-related cortisol may be elevated or attenuated; heterogeneous data do not identify a subject's personal concentration trajectory"
  Attr.publicAttribution

crenshaw1991SituationalInterpretation : Attr.AttributedSource
crenshaw1991SituationalInterpretation = Attr.mkDOISource
  "Kimberle Williams Crenshaw"
  "Mapping the Margins: Intersectionality, Identity Politics, and Violence Against Women of Color"
  "Stanford Law Review 43(6), 1241-1299"
  "1991"
  "10.2307/1229039"
  "https://web.usca.edu/media/usca/departments/institutional-culture-amp-belonging/Crenshaw-MappingMarginsIntersectionality-1991.pdf"
  Attr.academicArticleSource
  "Motivates retaining situated institutional and relational constraints; not an endocrine study or a cortisol parameter source"
  Attr.publicAttribution

situatedCortisolSources : Attr.AttributedSourceAtlas
situatedCortisolSources = Attr.mkSourceAtlas
  "Situated cortisol/HPA source and interpretation boundary"
  "DASHI Governance with DASHI Biology owner reuse"
  (dickersonKemeny2004 ∷ khouryEnlowPlamondonLyonsRuth2019
   ∷ crenshaw1991SituationalInterpretation ∷ [])
  "Meta-analytic endocrine evidence, intersectional conceptual motivation, and DASHI mathematics are attributed separately"

cortisolSourceCount : Attr.sourceCount
  (Attr.sources situatedCortisolSources) ≡ 3
cortisolSourceCount = refl

cortisolAtlasIsNotPhysiologyProof :
  Attr.atlasCreatesAuthority situatedCortisolSources ≡ false
cortisolAtlasIsNotPhysiologyProof = refl
