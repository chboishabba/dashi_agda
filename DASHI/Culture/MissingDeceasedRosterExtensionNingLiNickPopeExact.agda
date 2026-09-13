module DASHI.Culture.MissingDeceasedRosterExtensionNingLiNickPopeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.LiTorrTheorySourceDiligenceProofSearchExact as Theory
import DASHI.Physics.ExoticGravity.NingLiYBCOGravityConstraintBidiExact as NingExperiment

------------------------------------------------------------------------
-- FULL-SET ROSTER EXTENSION
--
-- These rows repair two identities present in the broader missing-scientists /
-- UAP narrative but absent from the prior focused work-coverage ledger.
-- Ning Li has scientific work and an experimental constraint.  Nick Pope is a
-- civil-service/UFO-investigation/media role carrier, not a scientist.
------------------------------------------------------------------------

data RosterExtensionKind : Set where
  scientificWorkIdentity
  nonScientificNarrativeRole : RosterExtensionKind

record RosterExtensionReceipt : Set where
  constructor roster-extension-receipt
  field
    person : String
    kind : RosterExtensionKind
    eventIdentitySource : String
    eventDate : String
    roleOrWork : String
    stableWorkIdentifiers : String
    eventWorkIdentityPaid : Bool
    causeOrMannerIndependentlyPaid : Bool
    scientificWorkOwner : String
    nextExactLeaf : String

open RosterExtensionReceipt public

ningLiRosterRepair : RosterExtensionReceipt
ningLiRosterRepair = roster-extension-receipt
  "Ning Li"
  scientificWorkIdentity
  "Berryhill Funeral Home obituary: Ning Li of Huntsville, Alabama, died 2021-07-27; obituary identifies her with superconductivity/antigravity research"
  "2021-07-27"
  "University of Alabama in Huntsville superconducting-gravity theory; Li/Torr theory papers; 1997 static YBCO gravimeter experiment; later AC Gravity LLC research lineage reported publicly"
  "10.1103/PhysRevD.43.457; 10.1103/PhysRevB.46.5489; 10.1007/BF00665654; 10.1016/S0921-4534(97)01462-7"
  true false
  "LiTorrTheorySourceDiligenceProofSearchExact + NingLiYBCOGravityConstraintBidiExact"
  "primary UAH/employment and AC Gravity corporate/DoD award lineage; exact 2001 Other Transaction identifier and released technical results; event cause from independent medical/official carrier if public"

nickPopeRosterRepair : RosterExtensionReceipt
nickPopeRosterRepair = roster-extension-receipt
  "Nicholas George Pope"
  nonScientificNarrativeRole
  "BUFORA memorial reports former UK Ministry of Defence UFO investigator Nick Pope died 2026-04-06; independent memorial reporting identifies cancer"
  "2026-04-06"
  "former UK Ministry of Defence civil servant associated with UFO investigations; later author/media commentator"
  "no scientific DOI owner; role/event identity only"
  true false
  "none: non-scientist control/role carrier"
  "primary UK MoD service/role chronology and any exact event-time UAP disclosure/testimony obligation; do not manufacture scientific status from UFO-investigation role"

ningLiEventWorkIdentityPaid : Bool
ningLiEventWorkIdentityPaid = true

nickPopeIsNotScientist : Bool
nickPopeIsNotScientist = true

ningLiTheoryOwnerPresent : Theory.prd1991Candidate ≡ Theory.prd1991Candidate
ningLiTheoryOwnerPresent = refl

ningLiConstraintOwnerPresent :
  NingExperiment.staticYBCO1997Constraint ≡ NingExperiment.staticYBCO1997Constraint
ningLiConstraintOwnerPresent = refl

record RosterExtensionBoundary : Set where
  constructor roster-extension-boundary
  field
    conspiracyRosterMembershipCreatesScientificStatus : Bool
    obituaryIdentityPaysIndependentForensicCause : Bool
    ningLiNegativeExperimentMayConstrainTheorySearch : Bool
    nickPopeRoleMayBeUsedAsNonScientistControl : Bool
    ufoInvestigationRoleImpliesAccessToRecoveredCraft : Bool

canonicalRosterExtensionBoundary : RosterExtensionBoundary
canonicalRosterExtensionBoundary = roster-extension-boundary
  false false true true false
