module DASHI.Physics.Plasma.Phase243NumberRoleProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.NumberRoleProvenanceAtlasExact as Atlas
import DASHI.Moonshine.MonsterOgg279ProvenanceHubExact as N279

------------------------------------------------------------------------
-- NUMBER-ROLE PROVENANCE CROSS-POLLINATION
--
-- Current master owns NumberRoleProvenanceAtlasExact precisely to prevent a
-- shared printed scalar from collapsing distinct mathematical/source roles.
-- The plasma 243/270/276 lane adopts that discipline directly.
------------------------------------------------------------------------

data PlasmaCarrierNumberRole : Set where
  phaseCore243Role : PlasmaCarrierNumberRole
  phaseRook270Role : PlasmaCarrierNumberRole
  magnetDuad276Role : PlasmaCarrierNumberRole

record PlasmaNumberProvenanceEntry : Set where
  constructor plasma-number-provenance-entry
  field
    printedValue : String
    role : PlasmaCarrierNumberRole
    meaning : String
    repoOwner : String
    evidenceRelation : Atlas.EvidenceRelation

open PlasmaNumberProvenanceEntry public

phase243Entry : PlasmaNumberProvenanceEntry
phase243Entry =
  plasma-number-provenance-entry
    "243"
    phaseCore243Role
    "action-invariant non-axis rook-incidence core with F3^2 phase fibre; explicit F3^5 carrier"
    "DASHI.Physics.Plasma.PhaseRook270Exact / PhaseCore243FiveTritExact"
    Atlas.currentRepoOwner

phase270Entry : PlasmaNumberProvenanceEntry
phase270Entry =
  plasma-number-provenance-entry
    "270"
    phaseRook270Role
    "30 rook-related harmonic-plane incidences times a nine-state phase fibre"
    "DASHI.Physics.Plasma.PhaseRook270Exact"
    Atlas.currentRepoOwner

magnet276Entry : PlasmaNumberProvenanceEntry
magnet276Entry =
  plasma-number-provenance-entry
    "276"
    magnetDuad276Role
    "unordered support pairs of the 24 free real-coordinate chart; Pair24 carrier recognition only"
    "DASHI.Physics.Plasma.ToroidalZeroBounceM24DuadRecognitionExact"
    Atlas.currentRepoOwner

plasma243Plus27Plus9Hits279 : 243 + 27 + 9 ≡ N279.single279
plasma243Plus27Plus9Hits279 = N279.ternarySparseExpansionIs279

record PhaseNumberProvenanceBoundary : Set where
  constructor phase-number-provenance-boundary
  field
    shared243ScalarCreatesMoonshineIdentity : Bool
    shared243ScalarCreatesMoonshineIdentityIsFalse :
      shared243ScalarCreatesMoonshineIdentity ≡ false
    shared276ScalarCreatesTwoBTateIdentity : Bool
    shared276ScalarCreatesTwoBTateIdentityIsFalse :
      shared276ScalarCreatesTwoBTateIdentity ≡ false
    arithmetic279CompletionCreatesMonsterIdentity : Bool
    arithmetic279CompletionCreatesMonsterIdentityIsFalse :
      arithmetic279CompletionCreatesMonsterIdentity ≡ false
    canonicalNumberRoleFirewallReused : Bool
    canonicalNumberRoleFirewallReusedIsTrue :
      canonicalNumberRoleFirewallReused ≡ true

canonicalPhaseNumberProvenanceBoundary : PhaseNumberProvenanceBoundary
canonicalPhaseNumberProvenanceBoundary =
  phase-number-provenance-boundary false refl false refl false refl true refl
