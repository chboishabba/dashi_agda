module DASHI.Interop.SLRClaimFragmentProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- CLAIM-LOCAL FRAGMENT PROJECTION
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_claim_fragment_projection.py
--   schema = slr-claim-fragment-projection-v1
--
-- A labelled discourse path can pay a local fragment relation to a canonical
-- claim without paying the full source extent of that canonical claim.
------------------------------------------------------------------------

data BoundaryPayment : Set where
  exactBoundary : BoundaryPayment
  boundedBoundary : BoundaryPayment
  contextBoundary : BoundaryPayment
  unpaidBoundary : BoundaryPayment

record ClaimLocalFragment : Set where
  constructor claimLocalFragment
  field
    fragmentReference : String
    parserSentenceReference : String
    canonicalClaimReference : String
    speakerReference : String
    leftBoundaryPayment : BoundaryPayment
    rightBoundaryPayment : BoundaryPayment
    wholeClaimExtentPaid : Bool
    candidateOnly : Bool
    truthPromoted : Bool

open ClaimLocalFragment public

record IntermediateDiscourseFragment : Set where
  constructor intermediateDiscourseFragment
  field
    fragmentReference : String
    parserSentenceReference : String
    speakerReference : String
    canonicalClaimReferenceAssigned : Bool
    retained : Bool
    candidateOnly : Bool

open IntermediateDiscourseFragment public

wongC029LocalFragment : ClaimLocalFragment
wongC029LocalFragment = claimLocalFragment
  "spaCy-42:segment-0"
  "spaCy-42"
  "ABC730-2026-09-09-C029"
  "PENNY WONG"
  contextBoundary
  exactBoundary
  false
  true
  false

greberIntermediateFragment : IntermediateDiscourseFragment
greberIntermediateFragment = intermediateDiscourseFragment
  "spaCy-42:segment-1"
  "spaCy-42"
  "JACOB GREBER"
  false
  true
  true

husicC030LocalFragment : ClaimLocalFragment
husicC030LocalFragment = claimLocalFragment
  "spaCy-42:segment-2"
  "spaCy-42"
  "ABC730-2026-09-09-C030"
  "ED HUSIC"
  boundedBoundary
  contextBoundary
  false
  true
  false

shoebridgeC032LocalFragment : ClaimLocalFragment
shoebridgeC032LocalFragment = claimLocalFragment
  "spaCy-45:segment-0"
  "spaCy-45"
  "ABC730-2026-09-09-C032"
  "DAVID SHOEBRIDGE"
  contextBoundary
  boundedBoundary
  false
  true
  false

leeserC033LocalFragment : ClaimLocalFragment
leeserC033LocalFragment = claimLocalFragment
  "spaCy-45:segment-1"
  "spaCy-45"
  "ABC730-2026-09-09-C033"
  "JULIAN LEESER"
  boundedBoundary
  contextBoundary
  false
  true
  false

record ClaimFragmentProjectionBoundary : Set where
  constructor claimFragmentProjectionBoundary
  field
    localFragmentMayProjectToCanonicalClaim : Bool
    localFragmentPaysWholeClaimExtent : Bool
    intermediateSpeakerMayBeDropped : Bool
    intermediateSpeakerMayBeAssignedNeighbourClaim : Bool
    boundedBoundaryMayBeCalledExact : Bool
    projectionPromotesClaimTruth : Bool
    candidateOnly : Bool

open ClaimFragmentProjectionBoundary public

canonicalClaimFragmentProjectionBoundary : ClaimFragmentProjectionBoundary
canonicalClaimFragmentProjectionBoundary = claimFragmentProjectionBoundary
  true
  false
  false
  false
  false
  false
  true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LocalFragmentPaysWholeClaimExtent : Set where
data IntermediateSpeakerMayBeDropped : Set where
data IntermediateSpeakerInheritsNeighbourClaim : Set where
data BoundedBoundaryIsExact : Set where
data FragmentProjectionPromotesTruth : Set where

localFragmentDoesNotPayWholeClaim : LocalFragmentPaysWholeClaimExtent → ⊥
localFragmentDoesNotPayWholeClaim ()

intermediateSpeakerIsRetained : IntermediateSpeakerMayBeDropped → ⊥
intermediateSpeakerIsRetained ()

intermediateSpeakerDoesNotInheritClaim : IntermediateSpeakerInheritsNeighbourClaim → ⊥
intermediateSpeakerDoesNotInheritClaim ()

boundedIsNotExact : BoundedBoundaryIsExact → ⊥
boundedIsNotExact ()

fragmentProjectionDoesNotPromoteTruth : FragmentProjectionPromotesTruth → ⊥
fragmentProjectionDoesNotPromoteTruth ()
