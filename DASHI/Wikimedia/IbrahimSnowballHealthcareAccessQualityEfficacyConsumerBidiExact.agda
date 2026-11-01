module DASHI.Wikimedia.IbrahimSnowballHealthcareAccessQualityEfficacyConsumerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Governance.HealthcareEqualityInvariant as Equality
import DASHI.Governance.HealthcareAccessDistortion as Access

------------------------------------------------------------------------
-- IBRAHIM / HEALTHCARE CONCRETE CONSUMER
--
-- The existing healthcare invariant asks whether clinically equivalent need
-- receives equivalent accessible care.  That access/equality consumer does not
-- by itself establish clinical efficacy, health-care quality, population-level
-- public-health effect or governance adequacy.  Conversely, an efficacious
-- intervention does not manufacture access to it.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim healthcare access/quality/efficacy concrete consumer"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create access, efficacy, quality, equity, population effect or legal entitlement")

healthCareQid : Identity.ExternalIdentityDemand
healthCareQid = mkQid "health care" "Q31207"

publicHealthQid : Identity.ExternalIdentityDemand
publicHealthQid = mkQid "public health" "Q189603"

healthCareQualityQid : Identity.ExternalIdentityDemand
healthCareQualityQid = mkQid "health care quality" "Q17003063"

healthEquityQid : Identity.ExternalIdentityDemand
healthEquityQid = mkQid "health equity" "Q1512929"

healthServicesResearchQid : Identity.ExternalIdentityDemand
healthServicesResearchQid = mkQid "health services research" "Q5691150"

universalHealthCareQid : Identity.ExternalIdentityDemand
universalHealthCareQid = mkQid "universal health care / universal health coverage" "Q3274205"

healthServiceQid : Identity.ExternalIdentityDemand
healthServiceQid = mkQid "health service" "Q9353606"

clinicalEfficacyQid : Identity.ExternalIdentityDemand
clinicalEfficacyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim healthcare access/quality/efficacy concrete consumer"
  "external concept identity"
  "clinical efficacy / effectiveness as a general concept"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact general clinical-efficacy QID safely promoted; article/product-specific effectiveness items must not substitute for the concept")

healthCareDewey : Dewey.DeweyCoordinate
healthCareDewey = Dewey.mkUnresolvedDewey
  "health care"
  "no exact inspected DDC value promoted in this pass; medical/library classification remains navigation only"

publicHealthDewey : Dewey.DeweyCoordinate
publicHealthDewey = Dewey.mkUnresolvedDewey
  "public health"
  "no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- Sources. WHO is an institutional/normative source and legitimately has no
-- DOI here.  The Lancet source motivates quality as a separate health-system
-- axis rather than serving as a theorem about every health system.
------------------------------------------------------------------------

whoUniversalCoverageSource : Attribution.AttributedSource
whoUniversalCoverageSource = Attribution.mkNoDOISource
  "World Health Organization"
  "Universal health coverage"
  "WHO health topic / fact-sheet framework"
  "2025-2026 current web framework"
  "https://www.who.int/health-topics/universal-health-coverage"
  Attribution.institutionalSource
  "defines UHC through access to needed quality services without financial hardship and therefore keeps access, quality, need and financial protection as distinct coordinates"
  Attribution.publicAttribution

krukHighQualitySystemsSource : Attribution.AttributedSource
krukHighQualitySystemsSource = Attribution.mkDOISource
  "Margaret E. Kruk et al."
  "High-quality health systems in the Sustainable Development Goals era: time for a revolution"
  "The Lancet Global Health 6(11), e1196-e1252"
  "2018"
  "10.1016/S2214-109X(18)30386-3"
  "https://doi.org/10.1016/S2214-109X(18)30386-3"
  Attribution.academicArticleSource
  "health-system quality framework distinguishing access/coverage from effective high-quality care and health outcomes; does not establish efficacy of any specific intervention"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Existing exact healthcare access/equality machinery reused.
------------------------------------------------------------------------

data AccessEfficacyCase : Set where
  sameAccessEffectiveCare sameAccessIneffectiveCare : AccessEfficacyCase

data AccessSurface : Set where sameAccessibleCareSurface : AccessSurface
data EfficacyStatus : Set where clinicallyEffective clinicallyIneffective : EfficacyStatus

accessSurface : AccessEfficacyCase → AccessSurface
accessSurface _ = sameAccessibleCareSurface

efficacyStatus : AccessEfficacyCase → EfficacyStatus
efficacyStatus sameAccessEffectiveCare = clinicallyEffective
efficacyStatus sameAccessIneffectiveCare = clinicallyIneffective

accessEfficacyDefect : INF.NonFactorabilityWitness accessSurface efficacyStatus
accessEfficacyDefect = INF.nonFactorabilityWitness
  sameAccessEffectiveCare sameAccessIneffectiveCare refl (λ ())

accessCannotFactorClinicalEfficacy :
  INF.FactorsThrough accessSurface efficacyStatus → ⊥
accessCannotFactorClinicalEfficacy =
  INF.witnessRulesOutEveryFlatFactorisation accessEfficacyDefect

data EfficacyAccessCase : Set where
  sameEfficacyAccessible sameEfficacyInaccessible : EfficacyAccessCase

data EfficacySurface : Set where sameEffectiveIntervention : EfficacySurface
data AccessStatus : Set where interventionAccessible interventionNotAccessible : AccessStatus

efficacySurface : EfficacyAccessCase → EfficacySurface
efficacySurface _ = sameEffectiveIntervention

accessStatus : EfficacyAccessCase → AccessStatus
accessStatus sameEfficacyAccessible = interventionAccessible
accessStatus sameEfficacyInaccessible = interventionNotAccessible

efficacyAccessDefect : INF.NonFactorabilityWitness efficacySurface accessStatus
efficacyAccessDefect = INF.nonFactorabilityWitness
  sameEfficacyAccessible sameEfficacyInaccessible refl (λ ())

clinicalEfficacyCannotFactorAccess :
  INF.FactorsThrough efficacySurface accessStatus → ⊥
clinicalEfficacyCannotFactorAccess =
  INF.witnessRulesOutEveryFlatFactorisation efficacyAccessDefect

data CoverageCase : Set where
  sameCoverageHighQuality sameCoverageLowQuality : CoverageCase

data CoverageSurface : Set where sameServiceCoverage : CoverageSurface
data QualityStatus : Set where highQualityCare lowQualityCare : QualityStatus

coverageSurface : CoverageCase → CoverageSurface
coverageSurface _ = sameServiceCoverage

qualityStatus : CoverageCase → QualityStatus
qualityStatus sameCoverageHighQuality = highQualityCare
qualityStatus sameCoverageLowQuality = lowQualityCare

coverageQualityDefect : INF.NonFactorabilityWitness coverageSurface qualityStatus
coverageQualityDefect = INF.nonFactorabilityWitness
  sameCoverageHighQuality sameCoverageLowQuality refl (λ ())

coverageCannotFactorQuality : INF.FactorsThrough coverageSurface qualityStatus → ⊥
coverageCannotFactorQuality = INF.witnessRulesOutEveryFlatFactorisation coverageQualityDefect

data IndividualPopulationCase : Set where
  sameIndividualEffectBroadReach sameIndividualEffectNarrowReach : IndividualPopulationCase

data IndividualEffectSurface : Set where sameIndividualClinicalEffect : IndividualEffectSurface
data PopulationEffect : Set where broadPopulationImpact limitedPopulationImpact : PopulationEffect

individualEffectSurface : IndividualPopulationCase → IndividualEffectSurface
individualEffectSurface _ = sameIndividualClinicalEffect

populationEffect : IndividualPopulationCase → PopulationEffect
populationEffect sameIndividualEffectBroadReach = broadPopulationImpact
populationEffect sameIndividualEffectNarrowReach = limitedPopulationImpact

individualPopulationDefect : INF.NonFactorabilityWitness individualEffectSurface populationEffect
individualPopulationDefect = INF.nonFactorabilityWitness
  sameIndividualEffectBroadReach sameIndividualEffectNarrowReach refl (λ ())

individualEffectCannotFactorPopulationImpact :
  INF.FactorsThrough individualEffectSurface populationEffect → ⊥
individualEffectCannotFactorPopulationImpact =
  INF.witnessRulesOutEveryFlatFactorisation individualPopulationDefect

record HealthcareReverseConstraint : Set where
  constructor healthcare-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open HealthcareReverseConstraint public

healthcareConstraint : HealthcareReverseConstraint
healthcareConstraint = healthcare-reverse-constraint
  "Health care / health services"
  "clinical need, intervention efficacy, availability, accessibility, quality, affordability, equity and governance remain distinct"
  false

publicHealthConstraint : HealthcareReverseConstraint
publicHealthConstraint = healthcare-reverse-constraint
  "Public health / population health"
  "individual treatment effect, uptake/reach, population distribution, prevention context and population outcome remain distinct"
  false

record HealthcareAccessQualityEfficacyBoundary : Set where
  constructor healthcare-access-quality-efficacy-boundary
  field
    concreteHealthcareConsumerSelected : Bool
    qidsAttachedWhenSafelyResolved : Bool
    unresolvedClinicalEfficacyQidRetained : Bool
    deweyUnresolvedStatesRetained : Bool
    institutionalAndDoiSourcesRetained : Bool
    accessSeparatedFromEfficacy : Bool
    efficacySeparatedFromAccess : Bool
    coverageSeparatedFromQuality : Bool
    individualEffectSeparatedFromPopulationImpact : Bool
    existingHealthcareInvariantReused : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open HealthcareAccessQualityEfficacyBoundary public

canonicalHealthcareAccessQualityEfficacyBoundary : HealthcareAccessQualityEfficacyBoundary
canonicalHealthcareAccessQualityEfficacyBoundary =
  healthcare-access-quality-efficacy-boundary
    true true true true true true true true true true true false

-- Keep the actual existing governance carriers visibly in the dependency graph.
healthcareSystemCarrier : Set → Set → Set → Set₁
healthcareSystemCarrier = Equality.HealthcareSystem

accessDistortionCarrier : Access.DistortionAxis → Set
accessDistortionCarrier _ = Bool
