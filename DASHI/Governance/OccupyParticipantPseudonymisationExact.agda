module DASHI.Governance.OccupyParticipantPseudonymisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- PRIVACY-PRESERVING PARTICIPANT IDENTIFIERS FOR DERIVED OWS TABLES.
--
-- This is DASHI-derived privacy machinery, not an archival-source claim.
--
-- Policy:
--   * public source pages may contain names, but derived/formal incidence
--     tables use opaque participant IDs instead of propagating those names;
--   * IDs are six hexadecimal characters produced outside the repo by a keyed
--     HMAC-SHA256 namespace; the key and name<->ID map are not committed;
--   * equal canonical source labels receive equal IDs, allowing longitudinal
--     correlation without carrying names into the formal layer;
--   * spelling variants / aliases are NOT merged without a separate source-
--     justified identity-equivalence witness;
--   * collisions are audited; a colliding token must be lengthened rather than
--     silently identifying two people.
------------------------------------------------------------------------

record ParticipantToken : Set where
  constructor participantToken
  field
    shortHex : String

open ParticipantToken public

-- Current collision-audited tokens for the People's Library incidence tranche.
-- No raw participant names are stored in this owner.

p-ebddda : ParticipantToken
p-ebddda = participantToken "ebddda"

p-442ac6 : ParticipantToken
p-442ac6 = participantToken "442ac6"

p-aeedd2 : ParticipantToken
p-aeedd2 = participantToken "aeedd2"

p-81d19f : ParticipantToken
p-81d19f = participantToken "81d19f"

p-33f894 : ParticipantToken
p-33f894 = participantToken "33f894"

p-2b47b2 : ParticipantToken
p-2b47b2 = participantToken "2b47b2"

p-61309c : ParticipantToken
p-61309c = participantToken "61309c"

p-a936c6 : ParticipantToken
p-a936c6 = participantToken "a936c6"

p-b64222 : ParticipantToken
p-b64222 = participantToken "b64222"

p-bc1911 : ParticipantToken
p-bc1911 = participantToken "bc1911"

p-fc55c2 : ParticipantToken
p-fc55c2 = participantToken "fc55c2"

p-232026 : ParticipantToken
p-232026 = participantToken "232026"

p-f0412f : ParticipantToken
p-f0412f = participantToken "f0412f"

p-3d9d51 : ParticipantToken
p-3d9d51 = participantToken "3d9d51"

p-f4f5bb : ParticipantToken
p-f4f5bb = participantToken "f4f5bb"

p-c3fe3a : ParticipantToken
p-c3fe3a = participantToken "c3fe3a"

p-614e70 : ParticipantToken
p-614e70 = participantToken "614e70"

p-16fcb5 : ParticipantToken
p-16fcb5 = participantToken "16fcb5"

p-649768 : ParticipantToken
p-649768 = participantToken "649768"

p-7d95b2 : ParticipantToken
p-7d95b2 = participantToken "7d95b2"

currentAuditedTokenCount : Nat
currentAuditedTokenCount = 20

record PseudonymisationBoundary : Set where
  constructor pseudonymisationBoundary
  field
    rawNamesStoredInDerivedFormalTables : Bool
    hmacKeyCommittedToRepository : Bool
    privateNameTokenMapCommittedToRepository : Bool
    spellingVariantsAutomaticallyUnified : Bool
    shortTokenTreatedAsCryptographicAnonymityGuarantee : Bool
    sixHexCollisionAuditPassedForCurrentTwentyLabels : Bool
    collisionRequiresLengtheningOrRekeying : Bool
    stablePseudonymSupportsLongitudinalCorrelation : Bool
    publicSourceCitationRetained : Bool
    gitHistoryAutomaticallyPurgedByLiveTreeRedaction : Bool

open PseudonymisationBoundary public

canonicalPseudonymisationBoundary : PseudonymisationBoundary
canonicalPseudonymisationBoundary =
  pseudonymisationBoundary
    false false false false false
    true true true true false

canonicalOccupyParticipantPseudonymisationReceipt : GenericReceipt.GenericReceipt
canonicalOccupyParticipantPseudonymisationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "OWS participant pseudonymisation boundary"
    "DASHI.Governance.OccupyParticipantPseudonymisationExact"
    "canonicalPseudonymisationBoundary"
    "replaces raw participant labels in derived formal incidence tables with collision-audited six-hex keyed-HMAC pseudonyms while preserving stable within-namespace correlation and public source anchors"
    "the HMAC key and private name-token map are not committed; aliases are not merged without evidence; six-hex tokens are identifiers rather than a cryptographic anonymity guarantee; live-tree redaction does not purge prior Git history"
    "agda -i . DASHI/Governance/OccupyParticipantPseudonymisationRegression.agda"
