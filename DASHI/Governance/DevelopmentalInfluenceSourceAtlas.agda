module DASHI.Governance.DevelopmentalInfluenceSourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

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

merchantsOfDoubtHistory : ScholarlySource
merchantsOfDoubtHistory =
  mkSource
    "Naomi Oreskes; Erik M. Conway"
    "Merchants of Doubt: How a Handful of Scientists Obscured the Truth on Issues from Tobacco Smoke to Global Warming"
    "Bloomsbury Press, New York"
    "2010"
    "ISBN 978-1-59691-610-4; book, no DOI asserted"
    "historical genealogy source documenting recurring actors and doubt-production strategies across tobacco smoke, acid rain, ozone and climate controversies; does not establish one centrally commanded network"

oreskesConwayNatureCommentary : ScholarlySource
oreskesConwayNatureCommentary =
  mkSource
    "Naomi Oreskes; Erik M. Conway"
    "Defeating the merchants of doubt"
    "Nature 465:686-687"
    "2010"
    "DOI 10.1038/465686a"
    "concise scholarly commentary accompanying the historical genealogy; supports bounded cross-domain doubt-production vocabulary rather than a universal coordination claim"

blackwellExperimentComparison : ScholarlySource
blackwellExperimentComparison =
  mkSource
    "David Blackwell"
    "Equivalent Comparisons of Experiments"
    "The Annals of Mathematical Statistics 24(2):265-272"
    "1953"
    "DOI 10.1214/aoms/1177729032"
    "supports comparison-of-information vocabulary; DASHI supplies the exact observation-relative compression and separating-query theorems"

nissenbaumContextualIntegrity : ScholarlySource
nissenbaumContextualIntegrity =
  mkSource
    "Helen Nissenbaum"
    "Privacy as Contextual Integrity"
    "Washington Law Review 79(1):119-158"
    "2004"
    "journal citation; no DOI listed in the cited record"
    "supports context-relative information-flow vocabulary; does not by itself establish a legal or normative verdict for any named deployment"

washingtonAccessJusticeTechnologyPrinciples : ScholarlySource
washingtonAccessJusticeTechnologyPrinciples =
  mkSource
    "Washington State Access to Justice Board"
    "Washington State Access to Justice Technology Principles"
    "Washington Law Review 79(1):5"
    "2004"
    "journal citation; no DOI listed in the cited record"
    "supports access-to-justice vocabulary in which meaningful access includes procedural information and a just process includes timeliness, affordability and transparency; does not establish a binding legal threshold for the DASHI cost carrier"

cousotAbstractInterpretation : ScholarlySource
cousotAbstractInterpretation =
  mkSource
    "Patrick Cousot; Radhia Cousot"
    "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints"
    "POPL 1977:238-252"
    "1977"
    "DOI 10.1145/512950.512973"
    "supports abstraction/concrete-semantics vocabulary; DASHI supplies the consumer-relative future-safety and proxy/welfare trace theorems"

mooreKearfottCloudIntervalAnalysis : ScholarlySource
mooreKearfottCloudIntervalAnalysis =
  mkSource
    "Ramon E. Moore; R. Baker Kearfott; Michael J. Cloud"
    "Introduction to Interval Analysis"
    "SIAM, Other Titles in Applied Mathematics 110"
    "2009"
    "DOI 10.1137/1.9780898717716"
    "supports interval/enclosure vocabulary; DASHI supplies the abstract ordered-evidence composition theorem and does not infer empirical probabilities"

data SourceBoundary : Set where
  bibliographyIsNotCausality : SourceBoundary
  associationIsNotMechanism : SourceBoundary
  mechanismIsNotNormativeVerdict : SourceBoundary
  developmentalInfluenceIsNotIndoctrination : SourceBoundary
  politicalSimilarityIsNotCommonCommand : SourceBoundary
  oneTransferCaseIsNotUniversalIndustryGenealogy : SourceBoundary
  historicalContinuityIsNotCentralCoordination : SourceBoundary
  informationOrderIsNotGovernanceVerdict : SourceBoundary
  abstractionSafetyIsConsumerRelative : SourceBoundary
  accessPrincipleIsNotAutomaticLegalThreshold : SourceBoundary
  intervalEnclosureIsNotProbabilityClaim : SourceBoundary

canonicalSourceBoundaries : List SourceBoundary
canonicalSourceBoundaries =
  bibliographyIsNotCausality
  ∷ associationIsNotMechanism
  ∷ mechanismIsNotNormativeVerdict
  ∷ developmentalInfluenceIsNotIndoctrination
  ∷ politicalSimilarityIsNotCommonCommand
  ∷ oneTransferCaseIsNotUniversalIndustryGenealogy
  ∷ historicalContinuityIsNotCentralCoordination
  ∷ informationOrderIsNotGovernanceVerdict
  ∷ abstractionSafetyIsConsumerRelative
  ∷ accessPrincipleIsNotAutomaticLegalThreshold
  ∷ intervalEnclosureIsNotProbabilityClaim
  ∷ []
