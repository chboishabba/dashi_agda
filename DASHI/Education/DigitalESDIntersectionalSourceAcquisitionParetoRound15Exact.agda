module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound15Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- ROUND 15: ELIGIBLE-BUT-INVISIBLE / NON-DISCLOSING HIDDEN POPULATIONS.
--
-- Python/Pareto recutting after Round 14 selected `whoWasEligibleButMissing`
-- as the deepest remaining absence-audit residual. This round therefore does
-- not acquire another broad equity source. It targets studies that identify or
-- characterise people who belong to the relevant population but do not become
-- visible in the institutional/registered analytic carrier.
--
-- Attribution discipline:
--   * external papers own only their bounded empirical/source propositions;
--   * DASHI owns the finite non-factorability construction below;
--   * same research programme != same measurement object;
--   * DOI/QID/Dewey coordinates identify/navigate and never create authority;
--   * candidate acquisition != final corpus inclusion.
------------------------------------------------------------------------

data Round15Residual : Set where
  hiddenDisabledPopulationSizeAndCharacteristics : Round15Residual
  nondisclosureReasonsAndDynamicVisibility : Round15Residual
  crossEquityNondisclosureAndInstitutionalLegibility : Round15Residual

record Round15Candidate : Set where
  constructor round15-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    deweyState : String
    targetResidual : Round15Residual
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round15Candidate public

mkRound15Candidate :
  (source : Attr.AttributedSource) →
  Round15Residual →
  String →
  String →
  Round15Candidate
mkRound15Candidate source residual reading limitation =
  round15-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound15Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object publication QID recorded by round 15"))
    "Dewey coordinate unresolved; no nearest-label substitution"
    residual reading limitation false refl

------------------------------------------------------------------------
-- Grimes et al. 2017: disclosed + non-disclosed populations in one university.
------------------------------------------------------------------------

grimesHiddenPopulationSource : Attr.AttributedSource
grimesHiddenPopulationSource = Attr.mkDOISource
  "Susan Grimes; Jill Scevak; Erica Southgate; Rachel Buchanan"
  "Non-disclosing students with disabilities or learning challenges: characteristics and size of a hidden population"
  "The Australian Educational Researcher 44(4-5), 425-441"
  "2017"
  "10.1007/s13384-017-0242-y"
  "https://doi.org/10.1007/s13384-017-0242-y"
  Attr.academicArticleSource
  "Primary Australian regional-university study using an anonymous online survey and non-deficit 'learning challenge' framing to identify disclosed and institutionally non-disclosed disability/learning-challenge populations, estimate the hidden population, and examine characteristics associated with non-disclosure."
  Attr.publicAttribution

grimesHiddenCandidate : Round15Candidate
grimesHiddenCandidate = mkRound15Candidate
  grimesHiddenPopulationSource
  hiddenDisabledPopulationSizeAndCharacteristics
  "Direct P0 donor for whoWasEligibleButMissing: the realised institutional disclosure register is not the whole population of students experiencing disability/learning challenges. The study explicitly seeks a hidden, non-disclosing population that ordinary institutional visibility misses."
  "One Australian regional university and survey-based population estimation. The source does not establish the true hidden-population size for every institution, all disability groups, or digital-ESD deployments."

------------------------------------------------------------------------
-- Grimes et al. 2019: why institutionally non-disclosed students stay hidden.
------------------------------------------------------------------------

grimesStayingInvisibleSource : Attr.AttributedSource
grimesStayingInvisibleSource = Attr.mkDOISource
  "Susan Grimes; Erica Southgate; Jill Scevak; Rachel Buchanan"
  "University student perspectives on institutional non-disclosure of disability and learning challenges: reasons for staying invisible"
  "International Journal of Inclusive Education 23(6), 639-655"
  "2019"
  "10.1080/13603116.2018.1442507"
  "https://doi.org/10.1080/13603116.2018.1442507"
  Attr.academicArticleSource
  "Primary Australian higher-education study of institutionally non-disclosed students identified through a survey that reframed disability as 'learning challenge'. It examines reasons for remaining invisible, continuing disclosure deliberation, and difficulty with institutional disclosure processes."
  Attr.publicAttribution

grimesInvisibleCandidate : Round15Candidate
grimesInvisibleCandidate = mkRound15Candidate
  grimesStayingInvisibleSource
  nondisclosureReasonsAndDynamicVisibility
  "Pays the observer/mechanism side of the hidden-population residual: institutional invisibility can be a continuing situated decision/process rather than evidence that the eligible population is absent. Visibility therefore changes over time and with disclosure conditions."
  "Same research programme as the 2017 hidden-population study does not make this the same measurement object. Reasons for non-disclosure do not determine prevalence, causality, or one preferred institutional disclosure policy."

------------------------------------------------------------------------
-- Clark/Kusevskis-Hayes/Wilkinson 2018: hidden equity groups beyond disability.
------------------------------------------------------------------------

clarkInvisibleEquitySource : Attr.AttributedSource
clarkInvisibleEquitySource = Attr.mkDOISource
  "Colin Clark; Rita Kusevskis-Hayes; Matthew Wilkinson"
  "Enhancing Student Disclosure: Australia's Invisible Equity Students and Reasons for Nondisclosure in Australia's Tertiary Sector"
  "JANZSSA - Journal of the Australian and New Zealand Student Services Association 26(1), 28-41"
  "2018"
  "10.30688/janzssa.2018.05"
  "https://doi.org/10.30688/janzssa.2018.05"
  Attr.academicArticleSource
  "Australian tertiary-equity study/project article examining nondisclosure across students with disability, Indigenous students and domestic students from non-English-speaking backgrounds. It treats disclosure, institutional category definitions and hidden equity subpopulations as distinct policy/service-design concerns."
  Attr.publicAttribution

clarkCandidate : Round15Candidate
clarkCandidate = mkRound15Candidate
  clarkInvisibleEquitySource
  crossEquityNondisclosureAndInstitutionalLegibility
  "Prevents the hidden-population audit from collapsing into disability alone: multiple equity groups can be eligible for consideration/support yet remain institutionally invisible, and category/disclosure design affects which populations become legible."
  "Article/project evidence is bounded to Australian tertiary equity disclosure. Cross-equity comparison does not create one shared causal mechanism, Indigenous authority, disability evidence for non-disabled groups, or universal disclosure policy."

canonicalRound15Frontier : List Round15Candidate
canonicalRound15Frontier =
  grimesHiddenCandidate
  ∷ grimesInvisibleCandidate
  ∷ clarkCandidate
  ∷ []

------------------------------------------------------------------------
-- DASHI-owned constructive collision.
--
-- Same realised/registered carrier can coexist with distinct eligible hidden
-- populations. Therefore the realised carrier is insufficient to recover the
-- eligible-population state required by the who-is-not-at-the-table consumer.
------------------------------------------------------------------------

data HiddenPopulationWorld : Set where
  sameRegisteredSmallHiddenPopulation : HiddenPopulationWorld
  sameRegisteredLargeHiddenPopulation : HiddenPopulationWorld

data RealisedCarrierSurface : Set where
  sameRegisteredCarrier : RealisedCarrierSurface

realisedCarrierProjection : HiddenPopulationWorld → RealisedCarrierSurface
realisedCarrierProjection sameRegisteredSmallHiddenPopulation = sameRegisteredCarrier
realisedCarrierProjection sameRegisteredLargeHiddenPopulation = sameRegisteredCarrier

eligiblePopulationState : HiddenPopulationWorld → Bool
eligiblePopulationState sameRegisteredSmallHiddenPopulation = false
eligiblePopulationState sameRegisteredLargeHiddenPopulation = true

eligiblePopulationStatesDiffer :
  eligiblePopulationState sameRegisteredSmallHiddenPopulation ≡
  eligiblePopulationState sameRegisteredLargeHiddenPopulation → ⊥
eligiblePopulationStatesDiffer ()

hiddenPopulationWitness :
  Intersection.NonFactorabilityWitness realisedCarrierProjection eligiblePopulationState
hiddenPopulationWitness =
  Intersection.nonFactorabilityWitness
    sameRegisteredSmallHiddenPopulation
    sameRegisteredLargeHiddenPopulation
    refl
    eligiblePopulationStatesDiffer

HiddenPopulationFactorisation : Set₁
HiddenPopulationFactorisation =
  Intersection.FactorsThrough realisedCarrierProjection eligiblePopulationState

hiddenPopulationDoesNotFactorThroughRealisedCarrier :
  HiddenPopulationFactorisation → ⊥
hiddenPopulationDoesNotFactorThroughRealisedCarrier =
  Intersection.witnessRulesOutEveryFlatFactorisation hiddenPopulationWitness

------------------------------------------------------------------------
-- No-promotion / same-object firewalls.
------------------------------------------------------------------------

data Round15CandidateCreatesIncludedStudy : Set where
data RealisedCarrierCreatesEligiblePopulationState : Set where
data DisclosureRateCreatesEligiblePopulationTruth : Set where
data SameProgrammeCreatesSameMeasurementObject : Set where
data InstitutionalVisibilityCreatesPopulationTruth : Set where

round15CandidateDoesNotCreateIncludedStudy :
  Round15CandidateCreatesIncludedStudy → ⊥
round15CandidateDoesNotCreateIncludedStudy ()

realisedCarrierDoesNotCreateEligiblePopulationState :
  RealisedCarrierCreatesEligiblePopulationState → ⊥
realisedCarrierDoesNotCreateEligiblePopulationState ()

disclosureRateDoesNotCreateEligiblePopulationTruth :
  DisclosureRateCreatesEligiblePopulationTruth → ⊥
disclosureRateDoesNotCreateEligiblePopulationTruth ()

sameProgrammeDoesNotCreateSameMeasurementObject :
  SameProgrammeCreatesSameMeasurementObject → ⊥
sameProgrammeDoesNotCreateSameMeasurementObject ()

institutionalVisibilityDoesNotCreatePopulationTruth :
  InstitutionalVisibilityCreatesPopulationTruth → ⊥
institutionalVisibilityDoesNotCreatePopulationTruth ()

round15Reading : String
round15Reading =
  "The deepest post-Round-14 absence residual is eligible-but-missing. Grimes 2017 identifies and estimates a non-disclosing hidden disability/learning-challenge population; Grimes 2019 studies why such students remain institutionally invisible; Clark/Kusevskis-Hayes/Wilkinson broadens nondisclosure to multiple Australian equity groups. These sources motivate but do not own DASHI's finite collision showing that the same realised registered carrier can coexist with different eligible hidden populations. Candidate discovery, DOI identity, QID/Dewey navigation and disclosure counts do not create corpus admission, population truth or authority."
