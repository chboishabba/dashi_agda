module DASHI.Law.SensibLawParetoProofDirectedCorpusSearchBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierProofPromotionExact as Proof
import DASHI.Cognition.PNF.SensibLawNegligenceDutyGenericParetoFrontierExact as Duty
import DASHI.Cognition.PNF.SensibLawNegligenceDutyParetoProofPromotionExact as DutyProof
import DASHI.Law.HerzogColonialWrongTypeGenericParetoFrontierBridgeExact as Herzog
import DASHI.Law.HerzogColonialWrongTypeParetoProofPromotionExact as HerzogProof
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent

------------------------------------------------------------------------
-- PARETO-CERTIFIED FRONTIER -> PROOF-DIRECTED CORPUS SEARCH
--
-- DASHI synthesis. A Pareto proof certificate can justify scheduling a search
-- for a currently live proof gap. It does not pay that gap. The selected
-- producer/search mode remains independent from legal truth and authority.
------------------------------------------------------------------------

record CertifiedSearchDirective
    {Requirement : Set}
    {portfolio : List (Pareto.RequirementCandidate Requirement)}
    {selected : Pareto.RequirementCandidate Requirement}
    (promotion : Proof.FrontierPromotion portfolio selected) : Set where
  constructor certified-search-directive
  field
    producerClass : Intent.ProducerClass
    searchMode : Intent.SearchMode
    targetReference : String
    directiveReference : String

open CertifiedSearchDirective public

------------------------------------------------------------------------
-- Negligence / duty-of-care directives.
------------------------------------------------------------------------

corePolicySearchDirective :
  CertifiedSearchDirective DutyProof.corePolicyPromotion
corePolicySearchDirective = certified-search-directive
  Intent.authorityTreatmentProducer
  Intent.compareAuthorities
  "duty:core-government-policy"
  "The current duty Pareto certificate schedules authority/reasons comparison for the core-government-policy coordinate; it does not decide duty."

statutoryCoherenceSearchDirective :
  CertifiedSearchDirective DutyProof.statutoryCoherencePromotion
statutoryCoherenceSearchDirective = certified-search-directive
  Intent.exactCitedAuthorityProducer
  Intent.exploitKnownResidual
  "duty:statutory-coherence"
  "The post-policy Pareto certificate schedules primary/statutory authority recovery for statutory coherence; it does not establish a conflict."

------------------------------------------------------------------------
-- Herzog / colonial WrongType directives.
------------------------------------------------------------------------

herzogAuthorityMeaningSearchDirective :
  CertifiedSearchDirective HerzogProof.currentAuthorityPromotion
herzogAuthorityMeaningSearchDirective = certified-search-directive
  Intent.historicalContextProducer
  Intent.compareAuthorities
  "herzog:authority-meaning-before-after"
  "Recover source-bounded before/after authority-meaning evidence; structural analogy alone does not pay the translation."

herzogPowerPrerequisiteSearchDirective :
  CertifiedSearchDirective HerzogProof.afterAuthorityPowerPromotion
herzogPowerPrerequisiteSearchDirective = certified-search-directive
  Intent.authorityDiscoveryProducer
  Intent.exploitKnownResidual
  "herzog:operational-power-prerequisite"
  "Recover the exact rule/reasons making the asserted classification a prerequisite of the operational power, if such authority exists."

herzogIncidentWeldSearchDirective :
  CertifiedSearchDirective HerzogProof.afterPowerIncidentPromotion
herzogIncidentWeldSearchDirective = certified-search-directive
  Intent.occurrenceEvidenceProducer
  Intent.exploitKnownResidual
  "herzog:same-object-classification-order-unit-tactic-incident"
  "Recover same-object incident lineage evidence rather than treating document multiplicity or semantic repetition as causation."

------------------------------------------------------------------------
-- BIDI boundary: result assessment may close, defeat, or leave open the
-- scheduled requirement. Scheduling itself never performs that promotion.
------------------------------------------------------------------------

data SearchAssessmentDisposition : Set where
  sourceMayPayRequirement
  sourceMayActivateDefeater
  sourceLeavesRequirementOpen
  : SearchAssessmentDisposition

data ParetoCertificateAutomaticallyPaysProofGap : Set where
data SearchDirectiveCreatesAuthority : Set where
data RetrievedDocumentAutomaticallyPaysRequirement : Set where
data SchedulerMayOmitDefeaterSearch : Set where

aParetoCertificateOnlySchedules : ParetoCertificateAutomaticallyPaysProofGap → ⊥
aParetoCertificateOnlySchedules ()

directiveDoesNotCreateAuthority : SearchDirectiveCreatesAuthority → ⊥
directiveDoesNotCreateAuthority ()

retrievalStillNeedsAssessment : RetrievedDocumentAutomaticallyPaysRequirement → ⊥
retrievalStillNeedsAssessment ()

defeatersRemainLive : SchedulerMayOmitDefeaterSearch → ⊥
defeatersRemainLive ()
