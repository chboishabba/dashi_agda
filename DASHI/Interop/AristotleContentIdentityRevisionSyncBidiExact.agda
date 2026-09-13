module DASHI.Interop.AristotleContentIdentityRevisionSyncBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.CommutingProvenanceBidiCrossPollination2026Exact as Commuting
import DASHI.Core.TemporalPromotionNonRetroactivityBidiExact as Temporal
import DASHI.Interop.AristotleEvidenceSurfaceIdentityBoundaryExact as Identity

-- Archive donors: RequestProject.Publish / Archive / Sync.
record ContentRevisionSyncReceipt : Set where
  constructor content-revision-sync-receipt
  field
    canonicalContentReference : String
    contentIdentityReference : String
    entityRevisionReference : String
    graphRevisionReference : String
    revisionAlignmentReference : String
    commutingSyncReference : String
    sameCanonicalContent : Bool
    revisionsAligned : Bool
open ContentRevisionSyncReceipt public

-- Content identity, revision identity, revision alignment and semantic authority
-- remain separate coordinates.
data SameContentImpliesSameAuthority : Set where
data LaterAlignmentMakesEarlierRevisionAligned : Set where
data ContentIdentityImpliesRevisionAlignment : Set where

sameContentDoesNotCreateSameAuthority : SameContentImpliesSameAuthority → ⊥
sameContentDoesNotCreateSameAuthority ()

laterAlignmentIsNotRetroactive : LaterAlignmentMakesEarlierRevisionAligned → ⊥
laterAlignmentIsNotRetroactive ()

contentIdentityDoesNotCreateRevisionAlignment :
  ContentIdentityImpliesRevisionAlignment → ⊥
contentIdentityDoesNotCreateRevisionAlignment ()

record AristotleContentRevisionBoundary : Set where
  constructor aristotle-content-revision-boundary
  field
    contentIdentityDistinctFromRevisionIdentity : Bool
    revisionIdentityDistinctFromAlignment : Bool
    alignmentDistinctFromSemanticAuthority : Bool
    laterReceiptRetroactivelyPaysEarlierState : Bool
    commutingSyncPreservesProvenance : Bool

canonicalAristotleContentRevisionBoundary : AristotleContentRevisionBoundary
canonicalAristotleContentRevisionBoundary =
  aristotle-content-revision-boundary true true true false true

contentRevisionStatement : String
contentRevisionStatement =
  "Aristotle publication/archive/sync semantics support replay-stable content identity while keeping content identity, revision identity, revision alignment and semantic authority separate. A later alignment receipt extends later state only; it does not retroactively certify an earlier revision, and provenance-preserving sync must carry its commuting relation explicitly."
