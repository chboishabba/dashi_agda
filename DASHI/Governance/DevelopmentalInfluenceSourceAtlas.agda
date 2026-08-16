module DASHI.Governance.DevelopmentalInfluenceSourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source atlas for the developmental-influence / epistemic-dependency lane.
--
-- These records bind bibliographic provenance to bounded formal roles.  A
-- source entry does not by itself promote a causal, clinical, legal, religious
-- or political conclusion.
------------------------------------------------------------------------

record ScholarlySource : Set where
  constructor scholarlySource
  field
    authors : String
    title : String
    venue : String
    year : String
    identifier : String
    formalRole : String
    sourceCreatesCausalConclusion : Bool
    sourceCreatesNormativeConclusion : Bool

open ScholarlySource public

mkSource : String → String → String → String → String → String → ScholarlySource
mkSource a t v y i role = scholarlySource a t v y i role false false

sweetnessExposureReview : ScholarlySource
sweetnessExposureReview =
  mkSource
    "David J. Mela; Davide Risso"
    "Does sweetness exposure drive 'sweet tooth'?"
    "British Journal of Nutrition 131(11):1934-1944"
    "2024"
    "DOI 10.1017/S0007114524000485"
    "supports a fail-closed boundary against promoting sweetness exposure to a generalized later sweet-tooth mechanism"

feedingPracticesProspective : ScholarlySource
feedingPracticesProspective =
  mkSource
    "Holly A. Harris; Alice R. Kininmonth; Zeynep Nas; Ivonne P. M. Derks; Fiona Quigley; Pauline W. Jansen; Clare Llewellyn"
    "Prospective associations between early childhood parental feeding practices and eating disorder symptoms and disordered eating behaviors in adolescence"
    "International Journal of Eating Disorders 57(3):716-726"
    "2024"
    "DOI 10.1002/eat.24159"
    "supports evidence-gated modelling of nonresponsive feeding and later self-regulatory disturbance; effect sizes are small and cross-cohort findings are not uniform"

rewardProcessingModel : ScholarlySource
rewardProcessingModel =
  mkSource
    "Caitlin C. Clements; Karina Ascunce; Charles A. Nelson"
    "In Context: A Developmental Model of Reward Processing, With Implications for Autism and Sensitive Periods"
    "Journal of the American Academy of Child and Adolescent Psychiatry 62(11):1200-1216"
    "2023"
    "DOI 10.1016/j.jaac.2022.07.861"
    "supports component-wise developmental reward modelling rather than a single scalar preference variable"

epistemicTrustReview : ScholarlySource
epistemicTrustReview =
  mkSource
    "Elizabeth Li; Chloe Campbell; Nick Midgley"
    "Epistemic trust: a comprehensive review of empirical insights and implications for developmental psychopathology"
    "Research in Psychotherapy: Psychopathology, Process and Outcome 26(3):704"
    "2023"
    "DOI 10.4081/ripppo.2023.704"
    "supports selective and revisable trust allocation rather than treating children as uniformly credulous"

screenUseContextMetaAnalysis : ScholarlySource
screenUseContextMetaAnalysis =
  mkSource
    "Sumudu Mallawaarachchi; Jade Burley; Myrto Mavilidi; Steven J. Howard; Leon Straker; Lisa Kervin; Sally Staton; Nicole Hayes; Amanda Machell; Marina Torjinski; Brodie Brady; George Thomas; Sharon Horwood; Sonia L. J. White; Juliana Zabatiero; Clara Rivera; Dylan Cliff"
    "Early Childhood Screen Use Contexts and Cognitive and Psychosocial Outcomes: A Systematic Review and Meta-analysis"
    "JAMA Pediatrics 178(10):1017-1026"
    "2024"
    "DOI 10.1001/jamapediatrics.2024.2620"
    "supports context-sensitive screen modelling, including a separate co-use / responsive-social channel"

indoctrinationSpaceReasons : ScholarlySource
indoctrinationSpaceReasons =
  mkSource
    "Chris Hanks"
    "Indoctrination and the space of reasons"
    "Educational Theory 58(2):193-212"
    "2008"
    "DOI 10.1111/j.1741-5446.2008.00284.x"
    "philosophical counter-position: asymmetrical initiation into reasons need not itself amount to autonomy-destroying indoctrination"

conspiritualitySource : ScholarlySource
conspiritualitySource =
  mkSource
    "Giovanna Parmigiani"
    "Magic and Politics: Conspirituality and COVID-19"
    "Journal of the American Academy of Religion 89(2):506-529"
    "2021"
    "DOI 10.1093/jaarel/lfab053"
    "supports modelling cross-domain semantic bridges without treating spirituality, wellness or left-coded aesthetics as intrinsically extremist"

nationalSmokersAllianceSource : ScholarlySource
nationalSmokersAllianceSource =
  mkSource
    "Michael Givel"
    "Consent and counter-mobilization: the case of the national smokers alliance"
    "Journal of Health Communication 12(4):339-357"
    "2007"
    "DOI 10.1080/10810730701326002"
    "supports a historically bounded consent-engineering / counter-mobilization case rather than a generic hidden-coordination claim"

philipMorrisLunchablesPrimary : ScholarlySource
philipMorrisLunchablesPrimary =
  mkSource
    "Laura A. Schmidt"
    "Tobacco Industry Contributions to the Development of Ultraprocessed Food in the United States, 1985-2007: A Case Study of Lunchables"
    "American Journal of Public Health 116(7):940-949"
    "2026"
    "DOI 10.2105/AJPH.2026.308491; PMID 42233189; PMCID PMC13277455"
    "primary internal-document case study supporting a bounded Philip Morris tobacco-to-food R&D transfer witness, including consumer-driven product development and better-for-you reformulation; does not establish that all food engineering derives from tobacco"

data SourceBoundary : Set where
  bibliographyIsNotCausality : SourceBoundary
  associationIsNotMechanism : SourceBoundary
  mechanismIsNotNormativeVerdict : SourceBoundary
  developmentalInfluenceIsNotIndoctrination : SourceBoundary
  politicalSimilarityIsNotCommonCommand : SourceBoundary
  oneTransferCaseIsNotUniversalIndustryGenealogy : SourceBoundary

canonicalSourceBoundaries : List SourceBoundary
canonicalSourceBoundaries =
  bibliographyIsNotCausality
  ∷ associationIsNotMechanism
  ∷ mechanismIsNotNormativeVerdict
  ∷ developmentalInfluenceIsNotIndoctrination
  ∷ politicalSimilarityIsNotCommonCommand
  ∷ oneTransferCaseIsNotUniversalIndustryGenealogy
  ∷ []
