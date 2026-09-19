module DASHI.Wikimedia.MaboLiveIdentityLineageInteropExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboWorldObjectIdentityExact as Identity
import DASHI.Wikimedia.MaboP7d5SlrRuntimeReceiptExact as Runtime

------------------------------------------------------------------------
-- LIVE PG LINEAGE -> GOLDEN WORLD-IDENTITY ATTACHMENT
--
-- The runtime rows prove persistence of identity_class_ref coordinates at the
-- SLR production boundary.  This owner attaches those coordinates to the Agda
-- golden identity objects without equating persistence with truth, authority,
-- applicability, or proof.
------------------------------------------------------------------------

maboCaseIdentity : Identity.WorldObjectIdentity
maboCaseIdentity =
  Identity.world-object-identity
    "world-object:mabo-case-1992-hca-23"
    "case:[1992]-HCA-23"
    "Q1501525"
    "https://en.wikipedia.org/wiki/Mabo_v_Queensland_(No_2)"
    "oalc:case:[1992]-HCA-23"

record LiveLineageIdentityAttachment : Set where
  constructor live-lineage-identity-attachment
  field
    lineageReceipt : Runtime.LiveDiscoveryIdentityLineageReceipt
    goldenIdentity : Identity.WorldObjectIdentity
    identityClassMatchesGoldenIdentity : Bool
    persistenceObserved : Bool
    persistenceCreatesSemanticAuthority : Bool
    persistencePromotesApplicability : Bool
    persistenceCreatesClaimTruth : Bool
    persistenceCreatesAgdaProof : Bool

open LiveLineageIdentityAttachment public

liveMaboCaseIdentityAttachment : LiveLineageIdentityAttachment
liveMaboCaseIdentityAttachment =
  live-lineage-identity-attachment
    Runtime.liveMaboCaseLineage
    maboCaseIdentity
    true
    true
    false
    false
    false
    false

liveEddieMaboIdentityAttachment : LiveLineageIdentityAttachment
liveEddieMaboIdentityAttachment =
  live-lineage-identity-attachment
    Runtime.liveEddieMaboLineage
    Identity.eddieMaboIdentity
    true
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- The equalities below are source-level same-coordinate welds.  They connect
-- the live persisted identity_class_ref strings to the golden identities; they
-- do not assert that persistence caused the reviewed identity resolution.
------------------------------------------------------------------------

maboCaseLiveIdentityClassMatchesGolden :
  Runtime.identityClassRef Runtime.liveMaboCaseLineage
  ≡ Identity.identityClassReference maboCaseIdentity
maboCaseLiveIdentityClassMatchesGolden = refl

eddieMaboLiveIdentityClassMatchesGolden :
  Runtime.identityClassRef Runtime.liveEddieMaboLineage
  ≡ Identity.identityClassReference Identity.eddieMaboIdentity
eddieMaboLiveIdentityClassMatchesGolden = refl

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data PersistedIdentityClassEqualsSemanticAuthority : Set where
data PersistedIdentityClassEqualsClaimTruth : Set where
data PersistedIdentityClassEqualsApplicability : Set where
data PersistedIdentityClassEqualsAgdaProof : Set where
data PersistenceCreatesReviewedIdentityResolution : Set where

persistedIdentityClassDoesNotEqualSemanticAuthority :
  PersistedIdentityClassEqualsSemanticAuthority → ⊥
persistedIdentityClassDoesNotEqualSemanticAuthority ()

persistedIdentityClassDoesNotEqualClaimTruth :
  PersistedIdentityClassEqualsClaimTruth → ⊥
persistedIdentityClassDoesNotEqualClaimTruth ()

persistedIdentityClassDoesNotEqualApplicability :
  PersistedIdentityClassEqualsApplicability → ⊥
persistedIdentityClassDoesNotEqualApplicability ()

persistedIdentityClassDoesNotEqualAgdaProof :
  PersistedIdentityClassEqualsAgdaProof → ⊥
persistedIdentityClassDoesNotEqualAgdaProof ()

persistenceDoesNotCreateReviewedIdentityResolution :
  PersistenceCreatesReviewedIdentityResolution → ⊥
persistenceDoesNotCreateReviewedIdentityResolution ()
