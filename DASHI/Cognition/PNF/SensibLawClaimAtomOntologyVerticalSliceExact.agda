module DASHI.Cognition.PNF.SensibLawClaimAtomOntologyVerticalSliceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import ClaimReconciliationObjectLattice as Claims
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact as Base
import DASHI.Cognition.PNF.SensibLawClaimLatticeNarrativeStatusLiveBidiExact as Live

------------------------------------------------------------------------
-- CROSS-CARRIER VERTICAL SLICE
--
-- Older ClaimAtom and newer ITIR Claim/Perspective/Event are not treated as two
-- competing narrative worlds.  This record welds them by literal IDs and lets
-- the older typed claim discriminator refine the newer coarse assertion while
-- preserving reference identity and unresolved truth.
------------------------------------------------------------------------

record ClaimAtomOntologyWeld
    (atom : Claims.ClaimAtom)
    (claim : Ontology.Claim)
    (perspective : Ontology.Perspective)
    (event : Ontology.Event) : Set where
  constructor claimAtomOntologyWeld
  field
    samePropositionId :
      Claims.propositionId atom
      ≡ Ontology.StableId.value (Ontology.Claim.claimId claim)
    sameSpeaker :
      Ontology.Claim.assertedBy claim ≡ Ontology.Perspective.speakerId perspective
    sameEvent :
      Ontology.Claim.aboutEvent claim ≡ Ontology.Event.eventId event

open ClaimAtomOntologyWeld public

refinedOntologyProposition :
  Claims.ClaimAtom → Ontology.Claim → Status.PropositionStatusProduct
refinedOntologyProposition atom claim =
  Status.propositionStatusProduct
    (Ontology.StableId.value (Ontology.Claim.claimId claim))
    (Live.claimPropositionStatus (Claims.propositionType atom))
    Status.truthUnresolved
    Status.propositionSource
    Status.evidenceNeutral
    Status.sourceEvidence
    Status.modalityKindUnresolved
    Status.modalForceUnresolved
    Status.scopeUnresolved

record CrossCarrierPropositionReceipt
    {atom : Claims.ClaimAtom}
    {claim : Ontology.Claim}
    {perspective : Ontology.Perspective}
    {event : Ontology.Event}
    (weld : ClaimAtomOntologyWeld atom claim perspective event) : Set where
  constructor crossCarrierPropositionReceipt
  field
    coarse : Status.PropositionStatusProduct
    refined : Status.PropositionStatusProduct
    sameCoarseReference :
      Status.propositionReference coarse
      ≡ Ontology.StableId.value (Ontology.Claim.claimId claim)
    sameRefinedReference :
      Status.propositionReference refined
      ≡ Ontology.StableId.value (Ontology.Claim.claimId claim)
    sourceAtomSameReference :
      Claims.propositionId atom ≡ Status.propositionReference refined
    coarseTruthUnresolved :
      Status.truthStatus coarse ≡ Status.truthUnresolved
    refinedTruthUnresolved :
      Status.truthStatus refined ≡ Status.truthUnresolved
    resolution : Status.PropositionResolutionReceipt

open CrossCarrierPropositionReceipt public

compileCrossCarrierProposition :
  {atom : Claims.ClaimAtom} →
  {claim : Ontology.Claim} →
  {perspective : Ontology.Perspective} →
  {event : Ontology.Event} →
  (weld : ClaimAtomOntologyWeld atom claim perspective event) →
  CrossCarrierPropositionReceipt weld
compileCrossCarrierProposition {atom} {claim} weld =
  crossCarrierPropositionReceipt
    (Base.claimProposition claim)
    (refinedOntologyProposition atom claim)
    refl
    refl
    (samePropositionId weld)
    refl
    refl
    (Status.propositionResolutionReceipt
      (refinedOntologyProposition atom claim)
      (Live.claimPropositionStatus (Claims.propositionType atom))
      Status.truthUnresolved
      (Claims.propositionId atom)
      (Claims.provenanceNote atom ∷ [])
      "ClaimReconciliationObjectLattice.PropositionType")

------------------------------------------------------------------------
-- Event occurrence is stricter: the caller must also supply the indexed live
-- occurrence reading constructed by the claim-lattice bridge and prove that it
-- names the same literal ontology Event.
------------------------------------------------------------------------

record CrossCarrierOccurrenceReceipt
    {atom : Claims.ClaimAtom}
    {claim : Ontology.Claim}
    {perspective : Ontology.Perspective}
    {event : Ontology.Event}
    (weld : ClaimAtomOntologyWeld atom claim perspective event)
    (live : Live.LiveClaimOccurrenceReceipt atom) : Set where
  constructor crossCarrierOccurrenceReceipt
  field
    liveEventMatchesOntology :
      Live.eventReference live
      ≡ Ontology.StableId.value (Ontology.Event.eventId event)
    occurrenceResolution : Status.OccurrenceResolutionReceipt
    resultingOccurrenceExact :
      Status.resultingOccurrenceStatus occurrenceResolution
      ≡ Live.resultingOccurrence live

open CrossCarrierOccurrenceReceipt public

compileCrossCarrierOccurrence :
  {atom : Claims.ClaimAtom} →
  {claim : Ontology.Claim} →
  {perspective : Ontology.Perspective} →
  {event : Ontology.Event} →
  (weld : ClaimAtomOntologyWeld atom claim perspective event) →
  (live : Live.LiveClaimOccurrenceReceipt atom) →
  Live.eventReference live
    ≡ Ontology.StableId.value (Ontology.Event.eventId event) →
  CrossCarrierOccurrenceReceipt weld live
compileCrossCarrierOccurrence {atom} weld live eventEq =
  crossCarrierOccurrenceReceipt
    eventEq
    (Status.occurrenceResolutionReceipt
      (Live.eventStatus live)
      (Live.resultingOccurrence live)
      (Claims.propositionId atom ∷ [])
      (Claims.provenanceNote atom ∷ [])
      "indexed ClaimOccurrenceReading")
    refl

------------------------------------------------------------------------
-- Fully inhabited regression specimen from the existing canonical ClaimAtoms.
------------------------------------------------------------------------

dogSpeakerId : Ontology.StableId
dogSpeakerId = Ontology.stableId "actor:X"

dogPerspectiveId : Ontology.StableId
dogPerspectiveId = Ontology.stableId "perspective:dog-walk-fixture"

dogPerspective : Ontology.Perspective
dogPerspective =
  Ontology.perspectiveRecord dogPerspectiveId dogSpeakerId "claim-lattice fixture"

dogEvent : Ontology.Event
dogEvent =
  Ontology.event
    (Ontology.stableId "event:dog-walk")
    (Ontology.stableId "event-class:walk")
    "unspecified"
    "Whether X walked the dog."

dogWalkedOntologyClaim : Ontology.Claim
dogWalkedOntologyClaim =
  Ontology.claimRecord
    (Ontology.stableId "dog-walked-positive")
    (Ontology.Event.eventId dogEvent)
    dogSpeakerId
    "X walked the dog."
    dogPerspectiveId

dogDeniedOntologyClaim : Ontology.Claim
dogDeniedOntologyClaim =
  Ontology.claimRecord
    (Ontology.stableId "dog-walked-negative")
    (Ontology.Event.eventId dogEvent)
    dogSpeakerId
    "X did not walk the dog."
    dogPerspectiveId

dogWalkedWeld :
  ClaimAtomOntologyWeld
    Claims.canonicalDogWalkedClaim
    dogWalkedOntologyClaim
    dogPerspective
    dogEvent
dogWalkedWeld = claimAtomOntologyWeld refl refl refl

dogDeniedWeld :
  ClaimAtomOntologyWeld
    Claims.canonicalDogNotWalkedClaim
    dogDeniedOntologyClaim
    dogPerspective
    dogEvent
dogDeniedWeld = claimAtomOntologyWeld refl refl refl

dogWalkedPropositionLive : CrossCarrierPropositionReceipt dogWalkedWeld
dogWalkedPropositionLive = compileCrossCarrierProposition dogWalkedWeld

dogDeniedPropositionLive : CrossCarrierPropositionReceipt dogDeniedWeld
dogDeniedPropositionLive = compileCrossCarrierProposition dogDeniedWeld

dogWalkedOccurrenceLive :
  CrossCarrierOccurrenceReceipt dogWalkedWeld Live.canonicalDogWalkedOccurrence
dogWalkedOccurrenceLive =
  compileCrossCarrierOccurrence
    dogWalkedWeld Live.canonicalDogWalkedOccurrence refl

dogDeniedOccurrenceLive :
  CrossCarrierOccurrenceReceipt dogDeniedWeld Live.canonicalDogDeniedOccurrence
dogDeniedOccurrenceLive =
  compileCrossCarrierOccurrence
    dogDeniedWeld Live.canonicalDogDeniedOccurrence refl

canonicalPositiveIsAssertedNotAdmitted :
  Status.resultingOccurrenceStatus
    (CrossCarrierOccurrenceReceipt.occurrenceResolution dogWalkedOccurrenceLive)
  ≡ Status.assertedOccurrence
canonicalPositiveIsAssertedNotAdmitted = refl

canonicalDenialIsDeniedNotNegated :
  Status.resultingOccurrenceStatus
    (CrossCarrierOccurrenceReceipt.occurrenceResolution dogDeniedOccurrenceLive)
  ≡ Status.deniedOccurrence
canonicalDenialIsDeniedNotNegated = refl

canonicalBothTruthUnresolved :
  Status.resultingTruthStatus
    (CrossCarrierPropositionReceipt.resolution dogWalkedPropositionLive)
  ≡ Status.truthUnresolved
canonicalBothTruthUnresolved = refl

------------------------------------------------------------------------
-- No shortcut from the regression construction to real-world truth.
------------------------------------------------------------------------

data RegressionFixtureProvesWorldTruth : Set where

regressionFixtureDoesNotProveWorldTruth : RegressionFixtureProvesWorldTruth → ⊥
regressionFixtureDoesNotProveWorldTruth ()
