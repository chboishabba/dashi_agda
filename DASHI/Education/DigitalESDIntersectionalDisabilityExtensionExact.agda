module DASHI.Education.DigitalESDIntersectionalDisabilityExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- INTERSECTIONAL DISABILITY ACQUISITION EXTENSION
--
-- Source-local rule: disability/neurodivergence is not treated as a homogeneous
-- analytic carrier. The exact sampled groups, constructed comparison, missing
-- subgroups, response/exclusion surface and inferential ceiling stay attached
-- to the source that reported them.
------------------------------------------------------------------------

bonnetteIntersectionalitySource : Attr.AttributedSource
bonnetteIntersectionalitySource =
  Attr.mkDOISource
    "Rachel N. Bonnette; Samuel Abramovich; Adrienne Decker; Gregory A. Fabiano"
    "The Need for an ‘Intersectionality Variable’: Examining Differences in Challenging Experiences of Multiply Marginalised Neurodivergent Students in Higher Education STEM Programs"
    "International Journal of Disability, Development and Education"
    "2025"
    "10.1080/1034912X.2025.2571758"
    "https://doi.org/10.1080/1034912X.2025.2571758"
    Attr.academicArticleSource
    "Primary peer-reviewed quantitative/mixed survey analysis of neurodivergent STEM students, explicitly comparing singly and multiply marginalised respondents. It supports source-bounded group-difference claims, not universal prevalence, causal effects, or the experiences of marginalised subgroups too small to analyse separately."
    Attr.publicAttribution

waterfieldDisabilityComparatorSource : Attr.AttributedSource
waterfieldDisabilityComparatorSource =
  Attr.mkDOISource
    "Danielle A. Waterfield; Jaira Ferreira de Vasconcellos; Meriah Crawford; Mariane Doyle; Jessica Taggart; Breana Bayraktar; Dayna Henry"
    "Exploring Generative AI Use and Perceptions Among Students With and Without Disabilities in Higher Education"
    "Journal of Special Education Technology"
    "2026"
    "10.1177/01626434261454347"
    "https://doi.org/10.1177/01626434261454347"
    Attr.academicArticleSource
    "Primary cross-institutional survey source with 383 responses, including 48 students self-identifying as disabled. In the currently accessible abstract-level source surface it pays the existence and broad direction of a disability-status comparison, not detailed subgroup effect sizes, response denominators, or a transport claim."
    Attr.publicAttribution

bonnetteSurveyRespondentN : Nat
bonnetteSurveyRespondentN = 66

bonnetteAnalysisN : Nat
bonnetteAnalysisN = 54

waterfieldTotalRespondentN : Nat
waterfieldTotalRespondentN = 383

waterfieldDisabledRespondentN : Nat
waterfieldDisabledRespondentN = 48

------------------------------------------------------------------------
-- Bonnette et al. literal study-result PNF.
------------------------------------------------------------------------

bonnetteScope : PNF.AssertionScope
bonnetteScope = PNF.assertionScope
  "54 neurodivergent undergraduate/graduate students in STEM-related programmes retained for the analysed comparison"
  "one large public university in the north-east United States"
  "survey/needs-assessment comparison of singly versus multiply marginalised neurodivergent students"
  "singly marginalised neurodivergent respondents versus a constructed multiply marginalised indicator based on race/ethnicity, gender and/or additional disability"
  "self-reported variety and types of common neurodivergence-related STEM classroom challenges"
  "spring semester 2022 cross-sectional survey"

bonnettePredicates : List PNF.PredicateAtom
bonnettePredicates =
  PNF.predicateAtom "analysed-neurodivergent-stem-respondent" PNF.populationPredicate "respondent × STEM-programme"
    "54 respondents both answered the required prompts and self-identified as neurodivergent; 66 STEM respondents were present before exclusions"
  ∷ PNF.predicateAtom "intersectionality-comparator" PNF.comparatorPredicate "respondent × constructed-marginalisation-group"
    "comparison is between singly and multiply marginalised neurodivergent respondents using the source-defined indicator variable"
  ∷ PNF.predicateAtom "challenge-variety" PNF.outcomePredicate "respondent × reported-challenge-count"
    "RQ1 compares the variety of reported neurodivergence-related challenges with a Wilcoxon rank-sum test"
  ∷ PNF.predicateAtom "challenge-type" PNF.outcomePredicate "respondent × challenge-category"
    "chi-squared tests compare responses across ten types of experiences, with open-ended elaboration retained separately"
  ∷ PNF.predicateAtom "collapsed-intersectional-cells" PNF.contextPredicate "identity × analyzable-cell"
    "small racial-category cell sizes prevented separate analyses of specific multiply marginalised subgroups, so the study uses a constructed intersectionality variable"
  ∷ PNF.predicateAtom "response-and-selection-surface" PNF.contextPredicate "survey-frame × analysed-carrier"
    "participation was voluntary/anonymous and the analysed carrier excludes respondents missing required prompts or identifying as neurotypical; nonrespondent characteristics are not recovered"
  ∷ []

bonnetteIntersectionalContrastAssertion : PNF.PredicateNormalAssertion
bonnetteIntersectionalContrastAssertion = PNF.predicateNormalAssertion
  "bonnette-2025-intersectional-neurodivergent-stem-contrast"
  "Within the analysed neurodivergent STEM respondent sample, multiply marginalised respondents reported a wider variety and different pattern of challenging experiences than singly marginalised respondents."
  PNF.studyPopulationQ
  PNF.comparativeF
  bonnetteScope
  bonnettePredicates
  "same-object DOI 10.1080/1034912X.2025.2571758; n=66 STEM respondents before source-defined exclusions and n=54 analysed neurodivergent respondents"

bonnetteStrongestPaidImplication : Cone.ImplicationKind
bonnetteStrongestPaidImplication = Cone.derivesBoundedContrast

bonnetteFirstUnpaidImplication : Cone.ImplicationKind
bonnetteFirstUnpaidImplication = Cone.transportsPopulation

bonnetteWhoMissingReading : String
bonnetteWhoMissingReading =
  "The source itself identifies an intersectional visibility problem: multiply marginalised neurodivergent students can differ from singly marginalised peers, but small subgroup cells prevent separate race/gender/disability-specific analyses. The study does not recover nonrespondent experiences, cannot identify every omitted subgroup, and cannot justify treating one constructed intersectionality indicator as a complete representation of power or marginalisation."

waterfieldAcquisitionReading : String
waterfieldAcquisitionReading =
  "Waterfield et al. supplies a cross-institutional disability-status comparator with 383 responses, 48 from respondents self-identifying as disabled. The currently accessible primary publisher surface is abstract-level for this acquisition pass, so detailed subgroup statistics, response denominators and analysis-set handling remain acquisition debt rather than being borrowed from Zhao or other disability studies."

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data DisabilityLabelCreatesHomogeneousExperience : Set where
data IntersectionalityVariableCreatesCompleteIntersectionalRepresentation : Set where
data AnalyzedRespondentsRevealNonrespondents : Set where

disabilityLabelDoesNotCreateHomogeneousExperience : DisabilityLabelCreatesHomogeneousExperience → ⊥
disabilityLabelDoesNotCreateHomogeneousExperience ()

intersectionalityVariableDoesNotCreateCompleteRepresentation :
  IntersectionalityVariableCreatesCompleteIntersectionalRepresentation → ⊥
intersectionalityVariableDoesNotCreateCompleteRepresentation ()

analyzedRespondentsDoNotRevealNonrespondents : AnalyzedRespondentsRevealNonrespondents → ⊥
analyzedRespondentsDoNotRevealNonrespondents ()
