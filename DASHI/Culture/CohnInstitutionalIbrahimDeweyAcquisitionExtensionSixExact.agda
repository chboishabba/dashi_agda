module DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionSixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Culture.CohnInstitutionalIbrahimDeweyTraversalExact as Traversal
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFiveExact as Prior
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Governance.RelationalFlowGateAlgebra as Gate

------------------------------------------------------------------------
-- SIXTH IBRAHIM / QID / DEWEY ACQUISITION EXTENSION
--
-- P0 acquisition target: people who belong to the eligible/target population
-- but fail to enter the realised institutional or analytic carrier.
--
-- The three admitted sources pay distinct missingness mechanisms:
--   non-disclosure  != survey nonresponse != differential consent/opt-out.
--
-- They do not assert any fact about the synthetic Cohn fixture. They enlarge
-- the candidate observation family and motivate a separate finite DASHI
-- carrier theorem. Publication/author QIDs and publication-specific Dewey
-- remain unresolved unless a same-object record is independently verified.
------------------------------------------------------------------------

grimesHiddenPopulation : Source.AttributedSource
grimesHiddenPopulation = Source.mkDOISource
  "Susan Grimes; Jill Scevak; Erica Southgate; Rachel Buchanan"
  "Non-disclosing students with disabilities or learning challenges: characteristics and size of a hidden population"
  "The Australian Educational Researcher 44"
  "2017"
  "10.1007/s13384-017-0242-y"
  "https://doi.org/10.1007/s13384-017-0242-y"
  Source.academicArticleSource
  "Primary higher-education study of students with disabilities or learning challenges who remain institutionally hidden through non-disclosure. It motivates a non-disclosure missing-carrier coordinate: absence from disclosed/accommodation records does not establish absence from the eligible or affected population. It does not establish a fact about any other institution or prove a DASHI theorem."
  Source.publicAttribution

standishUmbachNonresponse : Source.AttributedSource
standishUmbachNonresponse = Source.mkDOISource
  "Trey Standish; Paul D. Umbach"
  "Should We Be Concerned About Nonresponse Bias in College Student Surveys? Evidence of Bias from a Validation Study"
  "Research in Higher Education 60(3), 338-357"
  "2019"
  "10.1007/s11162-018-9530-2"
  "https://doi.org/10.1007/s11162-018-9530-2"
  Source.academicArticleSource
  "Validation study comparing survey respondents and nonrespondents against administrative behavioural measures and finding topic-relevant response-propensity/nonresponse differences. It motivates a survey-nonresponse missing-carrier coordinate: realised respondents need not be representative of the target population. It does not license extrapolation to every survey or institution."
  Source.publicAttribution

liLearningAnalyticsConsent : Source.AttributedSource
liLearningAnalyticsConsent = Source.mkDOISource
  "Warren Li; Kaiwen Sun; Florian Schaub; Christopher Brooks"
  "Disparities in Students' Propensity to Consent to Learning Analytics"
  "International Journal of Artificial Intelligence in Education 32, 564-608"
  "2022"
  "10.1007/s40593-021-00254-2"
  "https://doi.org/10.1007/s40593-021-00254-2"
  Source.academicArticleSource
  "Study of student consent/opt-out propensity for learning analytics. The source explicitly treats differential participation or opt-out as capable of skewing the realised analytic population and predictive models. It motivates a differential-consent missing-carrier coordinate, not a universal claim that every opt-out process is biased."
  Source.publicAttribution

acquisitionExtensionSixAtlas : Source.AttributedSourceAtlas
acquisitionExtensionSixAtlas = Source.mkSourceAtlas
  "Cohn institutional Ibrahim/QID/Dewey acquisition extension six"
  "DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionSixExact"
  (grimesHiddenPopulation ∷ standishUmbachNonresponse ∷ liLearningAnalyticsConsent ∷ [])
  "Pareto tranche for eligible-but-missing populations. Non-disclosure, nonresponse and differential consent are retained as distinct gates. Source records expand the question set; they do not create institutional facts, import proof, or automatically select a repair."

------------------------------------------------------------------------
-- Identity / classification state.
------------------------------------------------------------------------

grimesIdentifierState : String
grimesIdentifierState =
  "DOI 10.1007/s13384-017-0242-y verified as bibliographic identity; publication-item and author Wikidata QIDs unresolved in this pass"

standishIdentifierState : String
standishIdentifierState =
  "DOI 10.1007/s11162-018-9530-2 verified as bibliographic identity; publication-item and author Wikidata QIDs unresolved in this pass"

liIdentifierState : String
liIdentifierState =
  "DOI 10.1007/s40593-021-00254-2 verified as bibliographic identity; publication-item and author Wikidata QIDs unresolved in this pass; similarly named researcher QIDs are not substituted without same-object evidence"

acquisitionSixDeweyState : String
acquisitionSixDeweyState =
  "publication-specific Dewey assignments unresolved; broad higher-education/research-method/data-analytics classes may guide navigation only and are not asserted as inspected publication classifications"

------------------------------------------------------------------------
-- Existing eligibility/gate owner reused as structural grammar.
------------------------------------------------------------------------

eligibilityGateCoordinatesKeptDistinct :
  {Eligible Assessment : Set} → Gate.DistinctCoordinates Eligible Assessment
eligibilityGateCoordinatesKeptDistinct = Gate.coordinatesKeptDistinct

------------------------------------------------------------------------
-- Candidate coordinate families.
------------------------------------------------------------------------

grimesNonDisclosureMissingCoordinate : Ibrahim.DashiKnowledgeCoordinate
grimesNonDisclosureMissingCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary higher-education source coordinate"
  "eligible/affected population hidden by disability or learning-challenge non-disclosure"
  "publication-specific Dewey unresolved"
  "publication and author QIDs unresolved"
  "doi:10.1007/s13384-017-0242-y"

grimesToEligibleButMissing : Ibrahim.DashiFirstLinkEdge
grimesToEligibleButMissing = Ibrahim.dashi-first-link-edge
  grimesNonDisclosureMissingCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "A disclosed/accommodation carrier can omit eligible or affected students who do not disclose. Non-disclosure must not be read as absence without an independent observation."
  true

standishNonresponseMissingCoordinate : Ibrahim.DashiKnowledgeCoordinate
standishNonresponseMissingCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary survey-validation source coordinate"
  "target-population members missing from realised survey carrier through nonresponse"
  "publication-specific Dewey unresolved"
  "publication and author QIDs unresolved"
  "doi:10.1007/s11162-018-9530-2"

standishToEligibleButMissing : Ibrahim.DashiFirstLinkEdge
standishToEligibleButMissing = Ibrahim.dashi-first-link-edge
  standishNonresponseMissingCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "A realised respondent surface can fail to carry target-population behaviour when response propensity covaries with topic-relevant behaviour. Nonresponse is therefore a candidate observation debt, not automatically ignorable missingness."
  true

liDifferentialConsentMissingCoordinate : Ibrahim.DashiKnowledgeCoordinate
liDifferentialConsentMissingCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary learning-analytics source coordinate"
  "eligible students omitted from realised analytic carrier through differential consent or opt-out"
  "publication-specific Dewey unresolved"
  "publication and author QIDs unresolved"
  "doi:10.1007/s40593-021-00254-2"

liToEligibleButMissing : Ibrahim.DashiFirstLinkEdge
liToEligibleButMissing = Ibrahim.dashi-first-link-edge
  liDifferentialConsentMissingCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Consent/opt-out is a distinct gate from response and disclosure. A realised learning-analytics carrier may differ from the eligible student population when participation propensity is differential."
  true

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AcquisitionSixBoundary : Set where
  constructor acquisition-six-boundary
  field
    eligibleButMissingFamilyAdded : Bool
    nonDisclosureGateAdded : Bool
    surveyNonresponseGateAdded : Bool
    differentialConsentGateAdded : Bool

    realisedCarrierEqualsEligiblePopulation : Bool
    nonDisclosureMeansNoDisability : Bool
    nonresponseMayBeIgnoredWithoutEvidence : Bool
    differentialConsentMayBeTreatedAsRandomMissingness : Bool

    disclosureResponseAndConsentAreDefinitionallySameGate : Bool
    sourceAdjacencyAutomaticallySelectsResidual : Bool
    sourceCreatesInstitutionalFact : Bool
    citationImportsProof : Bool
    unverifiedPublicationQidMayBeInvented : Bool
    deweyNeighbourMaySubstituteVerifiedPublicationClass : Bool

open AcquisitionSixBoundary public

canonicalAcquisitionSixBoundary : AcquisitionSixBoundary
canonicalAcquisitionSixBoundary = acquisition-six-boundary
  true true true true
  false false false false
  false false false false false false

grimesCitationDoesNotImportProof :
  Source.citationImportsProof grimesHiddenPopulation ≡ false
grimesCitationDoesNotImportProof = refl

standishCitationDoesNotImportProof :
  Source.citationImportsProof standishUmbachNonresponse ≡ false
standishCitationDoesNotImportProof = refl

liCitationDoesNotImportProof :
  Source.citationImportsProof liLearningAnalyticsConsent ≡ false
liCitationDoesNotImportProof = refl

------------------------------------------------------------------------
-- Pareto frontier after extension six.
------------------------------------------------------------------------

record AcquisitionSixFrontier : Set where
  constructor acquisition-six-frontier
  field
    p0Family : String
    admittedMechanisms : String
    qidDeweyDebt : String
    existingReuse : String
    nextProofUse : String
    stopRule : String

open AcquisitionSixFrontier public

canonicalAcquisitionSixFrontier : AcquisitionSixFrontier
canonicalAcquisitionSixFrontier = acquisition-six-frontier
  "whoWasEligibleButMissing / target population minus realised institutional or analytic carrier"
  "non-disclosure; survey nonresponse; differential learning-analytics consent/opt-out"
  "all three publication/author QID sets unresolved in this pass; publication-specific Dewey unresolved; DOI identities retained exactly"
  "RelationalFlowGateAlgebra already keeps eligibility distinct from a blocked gate/outcome; no new eligibility ontology is introduced"
  "construct a finite DASHI witness with the same realised carrier but materially different eligible/missing states, then expose missing-population recovery failure to proof-search/369 consumers"
  "do not add another missingness paper unless it adds a distinct gate or supplies a concrete observation for an existing unresolved eligible-but-missing fibre"
