module DASHI.Core.ParticipationSelectionQuotient where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ReopenableProjectionComposition as Reopenable

------------------------------------------------------------------------
-- PARTICIPATION / SELECTION BEFORE EXPRESSION
--
-- Reference / disciplinary motivation:
--   Peter Felten, Julianne Bagg, Michael Bumbry, Jennifer Hill, Karen Hornsby,
--   Maria Pratt, Saranne Weller,
--   "A call for expanding inclusive student engagement in SoTL",
--   Teaching & Learning Inquiry 1(2), 63-74 (2013).
--   DOI: 10.20343/teachlearninqu.1.2.63.
--
-- The paper motivates distinguishing who is privileged, discouraged, reached
-- and able to enter co-inquiry.  The exact residual pipeline below is DASHI's
-- formal construction; it is not an empirical model of that study.
------------------------------------------------------------------------

record PopulationState : Set where
  constructor populationState
  field
    eligibilityDistinction : Bool
    invitationReachDistinction : Bool
    participationDistinction : Bool
    expressionContent : Bool

open PopulationState public

record EligibleSurface : Set where
  constructor eligibleSurface
  field
    invitedAfterEligibility : Bool
    participatesAfterEligibility : Bool
    expressionAfterEligibility : Bool

open EligibleSurface public

record InvitedSurface : Set where
  constructor invitedSurface
  field
    participatesAfterInvitation : Bool
    expressionAfterInvitation : Bool

open InvitedSurface public

record ParticipatingSurface : Set where
  constructor participatingSurface
  field
    expressionAfterParticipation : Bool

open ParticipatingSurface public

eligibilityProjection : PopulationState → EligibleSurface
eligibilityProjection (populationState eligibility invited participates expression) =
  eligibleSurface invited participates expression

eligibilityReceipt : PopulationState → Bool
eligibilityReceipt (populationState eligibility invited participates expression) = eligibility

eligibilityReopen : EligibleSurface → Bool → PopulationState
eligibilityReopen (eligibleSurface invited participates expression) eligibility =
  populationState eligibility invited participates expression

eligibilityExact :
  (state : PopulationState) →
  eligibilityReopen (eligibilityProjection state) (eligibilityReceipt state) ≡ state
eligibilityExact (populationState eligibility invited participates expression) = refl

eligibilityMap :
  Reopenable.ExactReopenableProjection PopulationState EligibleSurface
eligibilityMap =
  Reopenable.exactReopenableProjection
    Bool eligibilityProjection eligibilityReceipt eligibilityReopen eligibilityExact

invitationProjection : EligibleSurface → InvitedSurface
invitationProjection (eligibleSurface invited participates expression) =
  invitedSurface participates expression

invitationReceipt : EligibleSurface → Bool
invitationReceipt (eligibleSurface invited participates expression) = invited

invitationReopen : InvitedSurface → Bool → EligibleSurface
invitationReopen (invitedSurface participates expression) invited =
  eligibleSurface invited participates expression

invitationExact :
  (state : EligibleSurface) →
  invitationReopen (invitationProjection state) (invitationReceipt state) ≡ state
invitationExact (eligibleSurface invited participates expression) = refl

invitationMap :
  Reopenable.ExactReopenableProjection EligibleSurface InvitedSurface
invitationMap =
  Reopenable.exactReopenableProjection
    Bool invitationProjection invitationReceipt invitationReopen invitationExact

participationProjection : InvitedSurface → ParticipatingSurface
participationProjection (invitedSurface participates expression) =
  participatingSurface expression

participationReceipt : InvitedSurface → Bool
participationReceipt (invitedSurface participates expression) = participates

participationReopen : ParticipatingSurface → Bool → InvitedSurface
participationReopen (participatingSurface expression) participates =
  invitedSurface participates expression

participationExact :
  (state : InvitedSurface) →
  participationReopen (participationProjection state) (participationReceipt state) ≡ state
participationExact (invitedSurface participates expression) = refl

participationMap :
  Reopenable.ExactReopenableProjection InvitedSurface ParticipatingSurface
participationMap =
  Reopenable.exactReopenableProjection
    Bool participationProjection participationReceipt participationReopen participationExact

populationToInvited :
  Reopenable.ExactReopenableProjection PopulationState InvitedSurface
populationToInvited =
  Reopenable.composeExactReopenableProjection eligibilityMap invitationMap

populationToParticipating :
  Reopenable.ExactReopenableProjection PopulationState ParticipatingSurface
populationToParticipating =
  Reopenable.composeExactReopenableProjection populationToInvited participationMap

preExpressionPipelineReopensExactly :
  (state : PopulationState) →
  Reopenable.reopen populationToParticipating
    (Reopenable.project populationToParticipating state)
    (Reopenable.receipt populationToParticipating state)
  ≡ state
preExpressionPipelineReopensExactly = Reopenable.reopenExact populationToParticipating

data SelectionExclusionIsNoAuthorityAfterParticipationPermission : Set where

selectionExclusionCannotCollapseIntoPostParticipationNoAuthority :
  SelectionExclusionIsNoAuthorityAfterParticipationPermission → ⊥
selectionExclusionCannotCollapseIntoPostParticipationNoAuthority ()
