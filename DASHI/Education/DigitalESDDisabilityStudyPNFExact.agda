module DASHI.Education.DigitalESDDisabilityStudyPNFExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact as Disability
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- DISABILITY STUDY RESULT -> PNF -> DESIGN-BOUNDED IMPLICATION
--
-- Each audit retains the exact attributed source object, the literal study
-- population/setting/outcome predicates, the available statistical surface,
-- the uncertainty surface, and the first unsupported promotion. No study is
-- promoted merely because its discussion recommends institutional action.
------------------------------------------------------------------------

record DisabilityStudyResultAudit : Set where
  constructor disability-study-result-audit
  field
    studyKey : String
    source : Attr.AttributedSource
    assertion : PNF.PredicateNormalAssertion
    statisticalReceipt : String
    uncertaintyReceipt : String
    strongestPaidImplication : Cone.ImplicationKind
    strongestPaidReason : String
    firstUnpaidImplication : Cone.ImplicationKind
    firstUnpaidReason : String
    promotionResidual : String

open DisabilityStudyResultAudit public

------------------------------------------------------------------------
-- Haider 2026: qualitative multiple-case access/use evidence.
------------------------------------------------------------------------

haiderScope : PNF.AssertionScope
haiderScope = PNF.assertionScope
  "10 purposively selected students with disabilities"
  "one public university in Bangladesh"
  "students' existing use of digital devices, software, apps and online services"
  "no intervention/control comparator"
  "reported access, engagement, purposes and contexts of digital-technology use"
  "cross-sectional qualitative fieldwork"

haiderPredicates : List PNF.PredicateAtom
haiderPredicates =
  PNF.predicateAtom "disabled-student-case" PNF.populationPredicate "student × disability × university"
    "participant is one of the ten purposively selected disabled university students"
  ∷ PNF.predicateAtom "technology-use" PNF.outcomePredicate "student × digital-technology"
    "participants report use of smartphones, laptops, software, apps and online services for academic and non-academic purposes"
  ∷ PNF.predicateAtom "access-context" PNF.contextPredicate "student × university-context"
    "technology use is interpreted through access and engagement in the local university context"
  ∷ PNF.predicateAtom "qualitative-elicitation" PNF.contextPredicate "interview × focus-group"
    "semi-structured interviews and focus-group discussion provide the evidence surface"
  ∷ []

haiderAssertion : PNF.PredicateNormalAssertion
haiderAssertion = PNF.predicateNormalAssertion
  "haider-2026-disabled-student-digital-access"
  "Among the ten purposively sampled disabled students, digital devices and services were used across academic and non-academic university activities, with access and engagement remaining context-dependent."
  PNF.studyPopulationQ
  PNF.descriptiveF
  haiderScope
  haiderPredicates
  "same-object DOI 10.1177/10554181251403851; abstract/methods report n=10 multiple-case qualitative study"

haiderResultAudit : DisabilityStudyResultAudit
haiderResultAudit = disability-study-result-audit
  "haider-2026-digital-access"
  Disability.haiderDigitalAccessSource
  haiderAssertion
  "n=10 purposively selected participants; no inferential effect estimate"
  "no confidence interval is applicable to the primary qualitative lived-experience/access claim"
  Cone.restatesMeasuredResult
  "the study pays source-bounded descriptions of access, use, engagement and context"
  Cone.transportsPopulation
  "one public-university purposive sample does not establish prevalence or transport across disabled students generally"
  "next proof-search target for prevalence would require a population-sampling design; another qualitative quotation cannot pay that obligation"

------------------------------------------------------------------------
-- Zhao, Cox & Chen 2025: descriptive survey/content-analysis evidence.
------------------------------------------------------------------------

zhaoScope : PNF.AssertionScope
zhaoScope = PNF.assertionScope
  "124 valid responses from students with disabilities"
  "one UK university"
  "self-directed use/non-use of generative AI in academic writing"
  "no randomized or non-user causal comparator"
  "reported uses, writing barriers, concerns, costs and desired institutional support/policy participation"
  "survey distributed February-March 2024"

zhaoPredicates : List PNF.PredicateAtom
zhaoPredicates =
  PNF.predicateAtom "disabled-student-respondent" PNF.populationPredicate "student × self-disclosed-disability"
    "respondent is one of 124 valid disabled-student survey cases"
  ∷ PNF.predicateAtom "genai-use" PNF.outcomePredicate "student × generative-AI"
    "96 of 124 respondents (77%) reported using generative AI"
  ∷ PNF.predicateAtom "writing-barriers" PNF.contextPredicate "student × academic-writing"
    "respondents report disability-related barriers including proofreading, reading, concentration, structuring ideas and time management"
  ∷ PNF.predicateAtom "subscription-cost" PNF.contextPredicate "student × affordability"
    "paid access is retained as a digital-inequality concern rather than collapsed into generic availability"
  ∷ PNF.predicateAtom "policy-voice" PNF.authorityPredicate "student × institutional-AI-policy"
    "respondents express a desire for involvement in institutional generative-AI policymaking"
  ∷ []

zhaoAssertion : PNF.PredicateNormalAssertion
zhaoAssertion = PNF.predicateNormalAssertion
  "zhao-cox-chen-2025-disabled-student-genai"
  "In the 124-response disabled-student survey, generative AI was widely used for academic-writing support while accuracy, integrity, affordability and institutional policy/training remained live concerns."
  PNF.studyPopulationQ
  PNF.descriptiveF
  zhaoScope
  zhaoPredicates
  "same-object DOI 10.1016/j.iheduc.2025.101014; n=124 valid responses; 77% (n=96) report GenAI use"

zhaoResultAudit : DisabilityStudyResultAudit
zhaoResultAudit = disability-study-result-audit
  "zhao-cox-chen-2025-genai-disability"
  Disability.zhaoCoxChenGenAISource
  zhaoAssertion
  "n=124 valid responses; 77% (n=96) report GenAI use; descriptive percentages and inductive content analysis"
  "no population-prevalence CI or causal-effect interval is reported for the main use/barrier/policy-voice claims"
  Cone.restatesMeasuredResult
  "the survey pays descriptive claims about this response set and source-bounded student preferences/concerns"
  Cone.attributesCausalEffect
  "self-selected descriptive survey data do not identify an effect of GenAI on learning, performance, engagement or equity"
  "next efficacy probe requires an estimand-specific comparative design; policy voice is a separate authority/participation coordinate rather than an efficacy outcome"

------------------------------------------------------------------------
-- Achtypi et al. 2026: lived-experience / institutional-context evidence.
------------------------------------------------------------------------

achtypiScope : PNF.AssertionScope
achtypiScope = PNF.assertionScope
  "20 undergraduate students with SpLDs and/or ASD plus 17 lecturers"
  "one mid-sized UK university"
  "existing technology-enhanced learning practices"
  "student and lecturer perspectives; no experimental control"
  "lived experience of flexibility, multimodal access, exclusionary context and institutional/pedagogical fit"
  "qualitative interview study"

achtypiPredicates : List PNF.PredicateAtom
achtypiPredicates =
  PNF.predicateAtom "student-lived-experience" PNF.populationPredicate "student × SpLD-or-ASD"
    "20 undergraduate students contribute first-person TEL experience"
  ∷ PNF.predicateAtom "lecturer-observer" PNF.populationPredicate "lecturer × TEL-practice"
    "17 lecturers contribute a distinct institutional/pedagogical observer fibre"
  ∷ PNF.predicateAtom "multimodal-flexibility" PNF.outcomePredicate "TEL × access"
    "participants describe flexibility and multimodal access as enabling in some contexts"
  ∷ PNF.predicateAtom "institutional-misalignment" PNF.contextPredicate "TEL × institutional-context"
    "institutional and pedagogical misalignment can mediate exclusion despite technology availability"
  ∷ []

achtypiAssertion : PNF.PredicateNormalAssertion
achtypiAssertion = PNF.predicateNormalAssertion
  "achtypi-2026-tel-neurodivergent-lived-experience"
  "Among interviewed students with SpLDs/ASD and lecturers, technology-enhanced learning was described as potentially enabling but conditional on inclusive pedagogy, infrastructure and institutional context."
  PNF.studyPopulationQ
  PNF.descriptiveF
  achtypiScope
  achtypiPredicates
  "same-object DOI 10.1002/berj.70039; 20 students and 17 lecturers interviewed"

achtypiResultAudit : DisabilityStudyResultAudit
achtypiResultAudit = disability-study-result-audit
  "achtypi-2026-tel-lived-experience"
  Disability.achtypiTELSource
  achtypiAssertion
  "20 student interviews + 17 lecturer interviews; qualitative thematic/lived-experience evidence, no population effect estimate"
  "no CI is applicable to the primary qualitative claim surface"
  Cone.restatesMeasuredResult
  "the study pays situated lived-experience and institutional-context predicates"
  Cone.transportsPopulation
  "single-institution qualitative evidence does not establish universal neurodivergent TEL effects or prevalence"
  "next transport probe requires deliberately broader sampling/context replication; adding more local themes does not itself create population transport"

------------------------------------------------------------------------
-- Yeterge 2026: explanatory sequential mixed-method sustainability evidence.
------------------------------------------------------------------------

yetergeScope : PNF.AssertionScope
yetergeScope = PNF.assertionScope
  "132 special-education teachers quantitatively; 20 selected teachers qualitatively"
  "teachers working with students with severe and multiple disabilities in multiple provinces of Turkiye"
  "existing assistive-technology use"
  "high- versus low-attitude qualitative groups; no student learning control condition"
  "teacher attitude plus reported technical/institutional conditions for sustainable assistive-technology use"
  "cross-sectional explanatory sequential mixed-method study"

yetergePredicates : List PNF.PredicateAtom
yetergePredicates =
  PNF.predicateAtom "teacher-attitude-score" PNF.outcomePredicate "teacher × assistive-technology-attitude"
    "132 teachers have mean attitude score 73.63/90 with SD 12.70"
  ∷ PNF.predicateAtom "qualitative-extreme-groups" PNF.comparatorPredicate "high-attitude × low-attitude-teacher"
    "20 interviewees were selected from higher and lower ends of the attitude-score distribution"
  ∷ PNF.predicateAtom "institutional-support" PNF.contextPredicate "school × support"
    "institutional support and professional development are reported as sustainability conditions"
  ∷ PNF.predicateAtom "maintenance-technical-support" PNF.contextPredicate "assistive-technology × continuity"
    "lack of technical support, device malfunction, time constraints and insufficient training are reported as barriers"
  ∷ PNF.predicateAtom "attitude-not-sufficient" PNF.contextPredicate "attitude × sustainable-use"
    "positive teacher attitudes coexist with implementation barriers, so attitude alone is not treated as sustainable-use payment"
  ∷ []

yetergeAssertion : PNF.PredicateNormalAssertion
yetergeAssertion = PNF.predicateNormalAssertion
  "yeterge-2026-assistive-technology-sustainability"
  "Teachers reported generally positive assistive-technology attitudes, while mixed-method evidence identified technical, institutional, training and maintenance conditions that constrain sustainable use."
  PNF.studyPopulationQ
  PNF.descriptiveF
  yetergeScope
  yetergePredicates
  "same-object DOI 10.3389/fpsyg.2026.1930074; quantitative n=132, qualitative n=20, M=73.63/90, SD=12.70"

yetergeResultAudit : DisabilityStudyResultAudit
yetergeResultAudit = disability-study-result-audit
  "yeterge-2026-assistive-technology-sustainability"
  Disability.yetergeAssistiveSustainabilitySource
  yetergeAssertion
  "quantitative n=132, M=73.63, SD=12.70; qualitative n=20; source reports training subgroup difference was not statistically significant"
  "no causal-effect CI for sustainable use or student outcomes is promoted; the descriptive attitude distribution and qualitative integration have different uncertainty semantics"
  Cone.restatesMeasuredResult
  "the mixed-method design pays bounded teacher-attitude and implementation-context findings"
  Cone.attributesCausalEffect
  "teacher attitudes/context reports do not identify a causal effect of assistive technology on student learning, participation or long-term sustainability"
  "next efficacy probe requires student-level outcomes and a causal/comparative design; next durability probe requires longitudinal continuity/maintenance observation"

primaryDisabilityStudyPNFAudits : List DisabilityStudyResultAudit
primaryDisabilityStudyPNFAudits =
  haiderResultAudit
  ∷ zhaoResultAudit
  ∷ achtypiResultAudit
  ∷ yetergeResultAudit
  ∷ []

primaryDisabilityStudyPNFCount : Nat
primaryDisabilityStudyPNFCount = 4

disabilityPrimaryStudiesPayUniversalDigitalLearningEffect : Bool
disabilityPrimaryStudiesPayUniversalDigitalLearningEffect = false
