module DASHI.Wikimedia.IbrahimSnowballManosphereGenderMasculinityYouthInfluenceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballManosphereIDWOnlineInfluenceBidiExact as Prior
import DASHI.Wikimedia.IbrahimSnowballSocialInfluenceConsentCoercionPrimarySourcesExact as Influence
import DASHI.Wikimedia.IbrahimSnowballPedagogyLearningBehaviorInteractionThirdOrderExact as Pedagogy

------------------------------------------------------------------------
-- BIDI continuation:
-- manosphere / online influence <-> masculinity / gender politics
-- <-> youth reception / humour / self-improvement <-> education / social influence.
--
-- QIDs are external identity/navigation only. Network membership, ideology,
-- endorsement, motive, causation and ethical status require separate receipts.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim manosphere/gender/youth BIDI"
  "verified external concept identity"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10; no semantic promotion")

feminismQid : Identity.ExternalIdentityDemand
feminismQid = mkQid "feminism" "Q7252"

antifeminismQid : Identity.ExternalIdentityDemand
antifeminismQid = mkQid "antifeminism" "Q575220"

misogynyQid : Identity.ExternalIdentityDemand
misogynyQid = mkQid "misogyny" "Q308857"

hegemonicMasculinityQid : Identity.ExternalIdentityDemand
hegemonicMasculinityQid = mkQid "hegemonic masculinity" "Q5698395"

mensRightsMovementQid : Identity.ExternalIdentityDemand
mensRightsMovementQid = mkQid "men's rights movement" "Q1292853"

incelQid : Identity.ExternalIdentityDemand
incelQid = mkQid "incel" "Q332395"

------------------------------------------------------------------------
-- Attributed current scholarship.
------------------------------------------------------------------------

privilegeThreatSource : Attribution.AttributedSource
privilegeThreatSource = Attribution.mkDOISource
  "Brooke Franklin-Paddock; Michael J. Platow; Michelle K. Ryan"
  "From Privilege to Threat: Unraveling Psychological Pathways to the Manosphere"
  "Archives of Sexual Behavior 54:1325-1340"
  "2025"
  "10.1007/s10508-025-03114-5"
  "https://doi.org/10.1007/s10508-025-03114-5"
  Attribution.academicArticleSource
  "two correlational studies of identity/threat variables and endorsement of selected manosphere attitudes in US men; does not establish deterministic causal pathway or membership"
  Attribution.publicAttribution

milneBakerSource : Attribution.AttributedSource
milneBakerSource = Attribution.mkDOISource
  "Betsy Milne; Catherine R. Baker"
  "From 'villains' to 'idols': exploring teenage boys' conflicting attachments to manospheric masculinities"
  "Gender and Education"
  "2025"
  "10.1080/09540253.2025.2568407"
  "https://doi.org/10.1080/09540253.2025.2568407"
  Attribution.academicArticleSource
  "focus-group/interview study of 12-17-year-olds in four London schools; retains ambivalence, humour and varying support rather than equating exposure with endorsement"
  Attribution.publicAttribution

halpinSource : Attribution.AttributedSource
halpinSource = Attribution.mkDOISource
  "Michael Halpin et al."
  "When Help Is Harm: Health, Lookism and Self-Improvement in the Manosphere"
  "Sociology of Health & Illness"
  "2025"
  "10.1111/1467-9566.70015"
  "https://doi.org/10.1111/1467-9566.70015"
  Attribution.academicArticleSource
  "qualitative study of a looksmaxxing/self-improvement community; health, body evaluation and hegemonic-masculinity interpretation remain source-bounded"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: engagement with the same manosphere-associated content cannot
-- recover endorsement because humour, critique, curiosity and support differ.
------------------------------------------------------------------------

data YouthReceptionCase : Set where
  sameContentCriticalHumour sameContentEndorsed : YouthReceptionCase

data ContentSurface : Set where sameManosphereContent : ContentSurface
data ReceptionReading : Set where criticalOrAmbivalent endorsedReading : ReceptionReading

contentSurface : YouthReceptionCase → ContentSurface
contentSurface _ = sameManosphereContent

receptionReading : YouthReceptionCase → ReceptionReading
receptionReading sameContentCriticalHumour = criticalOrAmbivalent
receptionReading sameContentEndorsed = endorsedReading

youthReceptionDefect : INF.NonFactorabilityWitness contentSurface receptionReading
youthReceptionDefect = INF.nonFactorabilityWitness
  sameContentCriticalHumour sameContentEndorsed refl (λ ())

contentCannotFactorYouthEndorsement :
  INF.FactorsThrough contentSurface receptionReading → ⊥
contentCannotFactorYouthEndorsement =
  INF.witnessRulesOutEveryFlatFactorisation youthReceptionDefect

------------------------------------------------------------------------
-- Regression 2: a self-improvement surface cannot recover its normative or
-- ideological role. Health practice, body discipline, commercial attention,
-- misogynistic discourse and ordinary self-care are not one atom.
------------------------------------------------------------------------

data SelfImprovementCase : Set where
  sameSelfImprovementOrdinaryCare sameSelfImprovementDominanceFrame : SelfImprovementCase

data SelfImprovementSurface : Set where sameSelfImprovementLabel : SelfImprovementSurface
data SelfImprovementRole : Set where ordinaryCareRole dominanceIdeologyRole : SelfImprovementRole

selfImprovementSurface : SelfImprovementCase → SelfImprovementSurface
selfImprovementSurface _ = sameSelfImprovementLabel

selfImprovementRole : SelfImprovementCase → SelfImprovementRole
selfImprovementRole sameSelfImprovementOrdinaryCare = ordinaryCareRole
selfImprovementRole sameSelfImprovementDominanceFrame = dominanceIdeologyRole

selfImprovementRoleDefect : INF.NonFactorabilityWitness selfImprovementSurface selfImprovementRole
selfImprovementRoleDefect = INF.nonFactorabilityWitness
  sameSelfImprovementOrdinaryCare sameSelfImprovementDominanceFrame refl (λ ())

selfImprovementCannotFactorIdeologicalRole :
  INF.FactorsThrough selfImprovementSurface selfImprovementRole → ⊥
selfImprovementCannotFactorIdeologicalRole =
  INF.witnessRulesOutEveryFlatFactorisation selfImprovementRoleDefect

------------------------------------------------------------------------
-- Regression 3: broad masculinity label cannot recover misogyny/antifeminism.
------------------------------------------------------------------------

data MasculinityCase : Set where
  masculinityWithoutMisogyny masculinityWithMisogynisticFrame : MasculinityCase

data MasculinitySurface : Set where sameMasculinitySurface : MasculinitySurface
data GenderPoliticsReading : Set where noMisogynyPaid misogynyPaid : GenderPoliticsReading

masculinitySurface : MasculinityCase → MasculinitySurface
masculinitySurface _ = sameMasculinitySurface

genderPoliticsReading : MasculinityCase → GenderPoliticsReading
genderPoliticsReading masculinityWithoutMisogyny = noMisogynyPaid
genderPoliticsReading masculinityWithMisogynisticFrame = misogynyPaid

masculinityPoliticsDefect : INF.NonFactorabilityWitness masculinitySurface genderPoliticsReading
masculinityPoliticsDefect = INF.nonFactorabilityWitness
  masculinityWithoutMisogyny masculinityWithMisogynisticFrame refl (λ ())

masculinityCannotFactorMisogyny :
  INF.FactorsThrough masculinitySurface genderPoliticsReading → ⊥
masculinityCannotFactorMisogyny =
  INF.witnessRulesOutEveryFlatFactorisation masculinityPoliticsDefect

------------------------------------------------------------------------
-- Reuse existing online/social-influence firewalls.
------------------------------------------------------------------------

priorOnlineBoundary : Prior.ManosphereIDWOnlineInfluenceBoundary
priorOnlineBoundary = Prior.canonicalManosphereIDWOnlineInfluenceBoundary

visibleComplianceStillDoesNotRecoverRelation :
  INF.FactorsThrough Influence.complianceSurface Influence.relationReading → ⊥
visibleComplianceStillDoesNotRecoverRelation = Influence.complianceCannotFactorRelation

pedagogyBoundary : Pedagogy.PedagogyLearningBehaviorInteractionBoundary
pedagogyBoundary = Pedagogy.canonicalPedagogyLearningBehaviorInteractionBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints to parents.
------------------------------------------------------------------------

record GenderYouthReverseConstraint : Set where
  constructor gender-youth-reverse-constraint
  field
    parentNode : String
    childWitness : String
    forcedDistinction : String
    parentMayEraseDistinction : Bool
open GenderYouthReverseConstraint public

socialInfluenceConstraint : GenderYouthReverseConstraint
socialInfluenceConstraint = gender-youth-reverse-constraint
  "Social influence"
  "youth reception of manosphere-associated content"
  "exposure, humour, ambivalence, peer performance, endorsement, private belief and action remain distinct"
  false

pedagogyConstraint : GenderYouthReverseConstraint
pedagogyConstraint = gender-youth-reverse-constraint
  "Pedagogy / informal learning"
  "self-improvement and manfluencer content"
  "learning or repetition does not establish source validity, learner agency, ethical permission or ideological assent"
  false

masculinityConstraint : GenderYouthReverseConstraint
masculinityConstraint = gender-youth-reverse-constraint
  "Masculinity"
  "hegemonic-masculinity/manosphere scholarship"
  "masculinity, hegemonic masculinity, misogyny, antifeminism and men's-rights movement are distinct identities/roles"
  false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ManosphereEqualsMensRightsMovement : Set where
data MasculinityEqualsMisogyny : Set where
data FeminismMentionCreatesThreat : Set where
data SelfImprovementCreatesManosphereMembership : Set where
data YouthExposureCreatesEndorsement : Set where
data CorrelationalPathCreatesDeterministicCause : Set where

manosphereDoesNotEqualMensRightsMovement : ManosphereEqualsMensRightsMovement → ⊥
manosphereDoesNotEqualMensRightsMovement ()

masculinityDoesNotEqualMisogyny : MasculinityEqualsMisogyny → ⊥
masculinityDoesNotEqualMisogyny ()

feminismMentionDoesNotCreateThreat : FeminismMentionCreatesThreat → ⊥
feminismMentionDoesNotCreateThreat ()

selfImprovementDoesNotCreateManosphereMembership : SelfImprovementCreatesManosphereMembership → ⊥
selfImprovementDoesNotCreateManosphereMembership ()

youthExposureDoesNotCreateEndorsement : YouthExposureCreatesEndorsement → ⊥
youthExposureDoesNotCreateEndorsement ()

correlationDoesNotCreateDeterministicCause : CorrelationalPathCreatesDeterministicCause → ⊥
correlationDoesNotCreateDeterministicCause ()

record ManosphereGenderMasculinityYouthBoundary : Set where
  constructor manosphere-gender-masculinity-youth-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    personNetworkAndIdeologyRolesRemainSeparate : Bool
    feminismAndAntifeminismRemainDistinctExternalIdentities : Bool
    masculinityDoesNotCollapseToMisogyny : Bool
    mensRightsMovementDoesNotCollapseToWholeManosphere : Bool
    youthExposureDoesNotDetermineEndorsement : Bool
    humourAmbivalenceAndSupportMayCoexist : Bool
    selfImprovementDoesNotDetermineIdeologicalRole : Bool
    correlationalEvidenceDoesNotCreateDeterministicCausation : Bool
    attributionTravelsWithEveryClassification : Bool
    reverseBidiConstraintsPropagateToParentNodes : Bool
    presentAxisVocabularyClaimedComplete : Bool
open ManosphereGenderMasculinityYouthBoundary public

canonicalManosphereGenderMasculinityYouthBoundary : ManosphereGenderMasculinityYouthBoundary
canonicalManosphereGenderMasculinityYouthBoundary =
  manosphere-gender-masculinity-youth-boundary
    true true true true true true true true true true true false
