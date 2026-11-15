module DASHI.Governance.Crenshaw1988SituatedVoiceExact where

-- Source: Kimberle Williams Crenshaw (1988), Race, Reform, and Retrenchment,
-- Harvard Law Review 101, 1331, note 2 (printed page 1331).
-- The author herself explains the choice between scholarly third-person
-- naming and a first-person "we" as a situated scholarly dilemma.
-- This is a directly located AUTHORIAL SELF-POSITIONING passage.
-- The finite model below is DASHI's own, not words attributed to Crenshaw
-- and not a claim that every Black scholar faces the same choice.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.CrenshawSituatedStandpointExact as Standpoint

data VoiceChoice : Set where
  thirdPersonDiscourse firstPersonSituatedVoice : VoiceChoice

data InstitutionalPublication : Set where
  sameProfessionalPublication : InstitutionalPublication

data AuthorRelation : Set where
  externallyClassifiedGroup authorIncludesSelf : AuthorRelation

data AuthorshipSituation : Set where
  externallyFramed situatedSelfPositioning : AuthorshipSituation

publicationLabel : AuthorshipSituation → InstitutionalPublication
publicationLabel externallyFramed = sameProfessionalPublication
publicationLabel situatedSelfPositioning = sameProfessionalPublication

voice : AuthorshipSituation → VoiceChoice
voice externallyFramed = thirdPersonDiscourse
voice situatedSelfPositioning = firstPersonSituatedVoice

authorRelation : AuthorshipSituation → AuthorRelation
authorRelation externallyFramed = externallyClassifiedGroup
authorRelation situatedSelfPositioning = authorIncludesSelf

samePublicationLabelDifferentVoice :
  INF.NonFactorabilityWitness publicationLabel voice
samePublicationLabelDifferentVoice =
  INF.nonFactorabilityWitness
    externallyFramed situatedSelfPositioning refl (λ ())

publicationLabelCannotRecoverAuthorPosition :
  INF.NonFactorabilityWitness publicationLabel authorRelation
publicationLabelCannotRecoverAuthorPosition =
  INF.nonFactorabilityWitness
    externallyFramed situatedSelfPositioning refl (λ ())

bibliographicLabelCannotRecoverSituatedVoice :
  INF.FactorsThrough publicationLabel voice → ⊥
bibliographicLabelCannotRecoverSituatedVoice =
  INF.witnessRulesOutEveryFlatFactorisation
    samePublicationLabelDifferentVoice

-- Neither a source's scholarly legitimacy nor its situated first-person
-- standpoint implies that the author was courtroom counsel for its subjects.
standpointDoesNotManufactureRepresentation :
  Standpoint.authorityOfRole Standpoint.scholarRole
  ≡ Standpoint.authorityOfRole Standpoint.counselRole → ⊥
standpointDoesNotManufactureRepresentation =
  Standpoint.scholarlyInterpretationIsNotClientRepresentation

-- A descriptive source receipt is not an adjudication of an institution.
data SourcePassageRole : Set where
  firstPersonAuthorReflection counselAppointmentRecord : SourcePassageRole

passageRolesNotInterchangeable :
  firstPersonAuthorReflection ≡ counselAppointmentRecord → ⊥
passageRolesNotInterchangeable ()

-- The real, independently documented passage is a source interpretive
-- anchor, not a value assigning either synthetic world to any person.
data SourceClaim : Set where
  situatedScholarVoiceDilemma : SourceClaim

record LocatedSelfPositioning (source : SourceClaim) : Set where
  constructor located-self-positioning
  field
    printedPage : Nat
    bibliographicLocator : String
    analyticScope : String

crenshaw1988PrefatoryNote : LocatedSelfPositioning
  situatedScholarVoiceDilemma
crenshaw1988PrefatoryNote =
  located-self-positioning 1331
    "Harvard Law Review volume 101, printed page 1331, author note 2"
    "Crenshaw expressly discusses the scholarly they/them vs we dilemma; does not appoint herself counsel in DeGraffenreid, Moore or Payne"
