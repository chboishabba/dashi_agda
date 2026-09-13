module DASHI.Wikimedia.IbrahimSnowballChildPsychologyDissentTeachingSecondOrderExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballChildhoodCategorisationConformityPsychologyBidiExact as Prior

------------------------------------------------------------------------
-- IBRAHIM / WIKIDATA SECOND-ORDER WALK: CHILDHOOD / SOCIAL PSYCHOLOGY
--
-- Follow only the active childhood/development/conformity lanes.  Stable QIDs
-- are navigation/provenance coordinates; external graph relations create search
-- obligations only and never empirical, ethical or authority payment.
--
--   child psychology          Q3411686
--   developmental psychology  Q175002
--   adaptation (psychology)   Q12761867
--   dissent                   Q1991663
--   teaching                  Q352842
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim second-order child/social-psychology walk"
  "verified external concept identity"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10")

childPsychologyQid : Identity.ExternalIdentityDemand
childPsychologyQid = mkQid "child psychology" "Q3411686"

developmentalPsychologyQid : Identity.ExternalIdentityDemand
developmentalPsychologyQid = mkQid "developmental psychology" "Q175002"

psychologicalAdaptationQid : Identity.ExternalIdentityDemand
psychologicalAdaptationQid = mkQid "adaptation (psychology)" "Q12761867"

dissentQid : Identity.ExternalIdentityDemand
dissentQid = mkQid "dissent" "Q1991663"

teachingQid : Identity.ExternalIdentityDemand
teachingQid = mkQid "teaching" "Q352842"

------------------------------------------------------------------------
-- Same adaptation surface cannot recover conformity versus dissent.
------------------------------------------------------------------------

data AdaptationCase : Set where adaptedByConformity adaptedWithDissent : AdaptationCase
data AdaptationSurface : Set where sameAdaptationSurface : AdaptationSurface
data SocialResponseReading : Set where conformityReading dissentReading : SocialResponseReading

adaptationSurface : AdaptationCase → AdaptationSurface
adaptationSurface _ = sameAdaptationSurface

socialResponseReading : AdaptationCase → SocialResponseReading
socialResponseReading adaptedByConformity = conformityReading
socialResponseReading adaptedWithDissent = dissentReading

adaptationResponseDefect : INF.NonFactorabilityWitness adaptationSurface socialResponseReading
adaptationResponseDefect = INF.nonFactorabilityWitness
  adaptedByConformity adaptedWithDissent refl (λ ())

adaptationCannotFactorResponseRole : INF.FactorsThrough adaptationSurface socialResponseReading → ⊥
adaptationCannotFactorResponseRole =
  INF.witnessRulesOutEveryFlatFactorisation adaptationResponseDefect

------------------------------------------------------------------------
-- Same teaching/discipline surface cannot recover child agency conditions.
------------------------------------------------------------------------

data TeachingCase : Set where sameTeachingContestable sameTeachingNoncontestable : TeachingCase
data TeachingSurface : Set where sameTeachingMethod : TeachingSurface
data AgencyReading : Set where contestableAgency noncontestableAgency : AgencyReading

teachingSurface : TeachingCase → TeachingSurface
teachingSurface _ = sameTeachingMethod

agencyReading : TeachingCase → AgencyReading
agencyReading sameTeachingContestable = contestableAgency
agencyReading sameTeachingNoncontestable = noncontestableAgency

teachingAgencyDefect : INF.NonFactorabilityWitness teachingSurface agencyReading
teachingAgencyDefect = INF.nonFactorabilityWitness
  sameTeachingContestable sameTeachingNoncontestable refl (λ ())

teachingCannotFactorChildAgency : INF.FactorsThrough teachingSurface agencyReading → ⊥
teachingCannotFactorChildAgency =
  INF.witnessRulesOutEveryFlatFactorisation teachingAgencyDefect

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data ChildDevelopmentEqualsChildPsychology : Set where
data DevelopmentalPsychologyEqualsChildPsychology : Set where
data AdaptationEqualsConformity : Set where
data ConformityEqualsObedience : Set where
data TeachingCreatesLegitimateAuthority : Set where

differentObjectStudyRelation : ChildDevelopmentEqualsChildPsychology → ⊥
differentObjectStudyRelation ()

overlappingDisciplinesNeedNotBeIdentical : DevelopmentalPsychologyEqualsChildPsychology → ⊥
overlappingDisciplinesNeedNotBeIdentical ()

adaptationDoesNotMeanConformity : AdaptationEqualsConformity → ⊥
adaptationDoesNotMeanConformity ()

conformityStillDoesNotMeanObedience : ConformityEqualsObedience → ⊥
conformityStillDoesNotMeanObedience ()

teachingDoesNotCreateLegitimateAuthority : TeachingCreatesLegitimateAuthority → ⊥
teachingDoesNotCreateLegitimateAuthority ()

record ChildSecondOrderSnowballBoundary : Set where
  constructor child-second-order-snowball-boundary
  field
    qidsRetainedWhenSafelyResolved : Bool
    wikidataRelationCreatesOnlySearchObligation : Bool
    childDevelopmentAndStudyDisciplineRemainDistinct : Bool
    conformityDissentObedienceRemainRoleDistinct : Bool
    teachingAndAuthorityRemainDistinct : Bool
    attributionTravelsWithNewAtoms : Bool
    nonfactorabilityCanReopenParentGraph : Bool
    presentVocabularyClaimedComplete : Bool
open ChildSecondOrderSnowballBoundary public

canonicalChildSecondOrderSnowballBoundary : ChildSecondOrderSnowballBoundary
canonicalChildSecondOrderSnowballBoundary = child-second-order-snowball-boundary
  true true true true true true true false

priorBoundary : Prior.ChildhoodCategorisationConformityPsychologyBidiBoundary
priorBoundary = Prior.canonicalChildhoodCategorisationConformityPsychologyBidiBoundary

discoveryBoundary : Discovery.SnowballDiscoveryBoundary
discoveryBoundary = Discovery.canonicalSnowballDiscoveryBoundary
