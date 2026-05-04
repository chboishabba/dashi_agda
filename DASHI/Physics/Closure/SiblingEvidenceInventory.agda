module DASHI.Physics.Closure.SiblingEvidenceInventory where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- SIB-R1: sibling-repo evidence inventory.
--
-- This module records useful evidence pointers discovered in sibling
-- repositories.  It is deliberately not an intake adapter and not a provider
-- receipt.  Any artifact named here must be re-run, checksum-bound, or adapted
-- through the relevant in-repo receipt lane before it can affect W3/W4/W5/W6/
-- W8/W9 promotion.

data SiblingEvidenceInventoryStatus : Set where
  siblingEvidenceFoundButReceiptsMissing :
    SiblingEvidenceInventoryStatus

data SiblingEvidenceKind : Set where
  dashifineHepProjectionCandidate :
    SiblingEvidenceKind
  dashifineLyapunovEnergyCandidate :
    SiblingEvidenceKind
  dashiQHepMirrorCandidate :
    SiblingEvidenceKind
  dashitestHepMirrorCandidate :
    SiblingEvidenceKind
  dashigLilaPhase2Trace :
    SiblingEvidenceKind
  dashigE8NamedVocabularyArtifact :
    SiblingEvidenceKind
  dashiLean4MoonshineArithmeticSupport :
    SiblingEvidenceKind

canonicalSiblingEvidenceKinds :
  List SiblingEvidenceKind
canonicalSiblingEvidenceKinds =
  dashifineHepProjectionCandidate
  ∷ dashifineLyapunovEnergyCandidate
  ∷ dashiQHepMirrorCandidate
  ∷ dashitestHepMirrorCandidate
  ∷ dashigLilaPhase2Trace
  ∷ dashigE8NamedVocabularyArtifact
  ∷ dashiLean4MoonshineArithmeticSupport
  ∷ []

record SiblingEvidenceEntry : Set where
  field
    evidenceKind :
      SiblingEvidenceKind

    siblingPath :
      String

    evidenceRole :
      String

    promotionBoundary :
      String

dashifineHepProjectionCandidateEntry :
  SiblingEvidenceEntry
dashifineHepProjectionCandidateEntry =
  record
    { evidenceKind =
        dashifineHepProjectionCandidate
    ; siblingPath =
        "../dashifine/hepdata_npz/phistar_50_76.npz; ../dashifine/hepdata_dashi_native/phistar_50_76_dashi_native_metrics.csv; ../dashifine/hepdata_to_dashi/phistar_50_76/"
    ; evidenceRole =
        "phi-star projection and DASHI-native metric candidate artifacts for routing the accepted prediction API lane"
    ; promotionBoundary =
        "read-only sibling candidate only; not a clean freeze, in-repo projection receipt, or comparison-law receipt"
    }

dashifineLyapunovEnergyCandidateEntry :
  SiblingEvidenceEntry
dashifineLyapunovEnergyCandidateEntry =
  record
    { evidenceKind =
        dashifineLyapunovEnergyCandidate
    ; siblingPath =
        "../dashifine/hepdata_lyapunov_test_out_all/overall_certification.json"
    ; evidenceRole =
        "Lyapunov and energy-functional candidate summary over HEPData/DASHI-native diagnostics"
    ; promotionBoundary =
        "energy-lane evidence pointer only; not empirical adequacy, not W3 authority, and not W9 pressure acceptance"
    }

dashiQHepMirrorCandidateEntry :
  SiblingEvidenceEntry
dashiQHepMirrorCandidateEntry =
  record
    { evidenceKind =
        dashiQHepMirrorCandidate
    ; siblingPath =
        "../dashiQ/temp_dashifine_quantum/hepdata_dashi_native/phistar_50_76_dashi_native_metrics.csv"
    ; evidenceRole =
        "mirrored or extended HEPData phi-star metrics useful for cross-checking the projection candidate path"
    ; promotionBoundary =
        "mirror artifact only; must not substitute for digest-bound t43/t44 artifacts or an in-repo DASHI projection run"
    }

dashitestHepMirrorCandidateEntry :
  SiblingEvidenceEntry
dashitestHepMirrorCandidateEntry =
  record
    { evidenceKind =
        dashitestHepMirrorCandidate
    ; siblingPath =
        "../dashitest/dashifine/"
    ; evidenceRole =
        "test-copy HEPData and dashifine artifacts that can help reproduce or compare sibling projection scripts"
    ; promotionBoundary =
        "test mirror only; no provider authority or promotion token is accepted from this path"
    }

dashigLilaPhase2TraceEntry :
  SiblingEvidenceEntry
dashigLilaPhase2TraceEntry =
  record
    { evidenceKind =
        dashigLilaPhase2Trace
    ; siblingPath =
        "../DASHIg/lila_phase2_validation/lila_external.csv; ../DASHIg/lila_phase2_validation/lila_external_delta_cone.csv"
    ; evidenceRole =
        "LILA Phase 2 execution trace and delta-cone summary evidence pointer"
    ; promotionBoundary =
        "execution trace only; not an E8 carrier, Lam-Tung adapter, theta/J bridge, or phi-star projection receipt"
    }

dashigE8NamedVocabularyArtifactEntry :
  SiblingEvidenceEntry
dashigE8NamedVocabularyArtifactEntry =
  record
    { evidenceKind =
        dashigE8NamedVocabularyArtifact
    ; siblingPath =
        "../DASHIg/LeechTransformer/vocab/e8_morpheme_.vocab; ../DASHIg/LeechTransformer/vocab/e8_morpheme_.model"
    ; evidenceRole =
        "E8-named tokenizer and vocabulary artifacts for the LILA/Leech engineering lane"
    ; promotionBoundary =
        "naming and engineering artifact only; no E8 root enumeration, inner product, Weyl action, or physics interpretation receipt"
    }

dashiLean4MoonshineArithmeticSupportEntry :
  SiblingEvidenceEntry
dashiLean4MoonshineArithmeticSupportEntry =
  record
    { evidenceKind =
        dashiLean4MoonshineArithmeticSupport
    ; siblingPath =
        "../dashi_lean4/MoonshineEarn.lean; ../dashi_lean4/MoonshineFractran.lean; ../dashi_lean4/DashiPerf/Audit.lean"
    ; evidenceRole =
        "Lean-side moonshine arithmetic and audit support that may guide a future Agda theta/J adapter"
    ; promotionBoundary =
        "sibling Lean evidence only; not imported as an Agda theorem and not a LILA-R4 theta/J receipt"
    }

canonicalSiblingEvidenceEntries :
  List SiblingEvidenceEntry
canonicalSiblingEvidenceEntries =
  dashifineHepProjectionCandidateEntry
  ∷ dashifineLyapunovEnergyCandidateEntry
  ∷ dashiQHepMirrorCandidateEntry
  ∷ dashitestHepMirrorCandidateEntry
  ∷ dashigLilaPhase2TraceEntry
  ∷ dashigE8NamedVocabularyArtifactEntry
  ∷ dashiLean4MoonshineArithmeticSupportEntry
  ∷ []

data SiblingEvidenceMissingReceipt : Set where
  missingAcceptedDashiPredictionAPI :
    SiblingEvidenceMissingReceipt
  missingCleanPredictionFreezeReceipt :
    SiblingEvidenceMissingReceipt
  missingDigestBoundProjectionReceipt :
    SiblingEvidenceMissingReceipt
  missingComparisonLawReceipt :
    SiblingEvidenceMissingReceipt
  missingE8CarrierReceipt :
    SiblingEvidenceMissingReceipt
  missingLamTungAdapterReceipt :
    SiblingEvidenceMissingReceipt
  missingThetaJAgdaAdapterReceipt :
    SiblingEvidenceMissingReceipt
  missingRuntimePNFReceipt :
    SiblingEvidenceMissingReceipt
  missingProviderAuthorityReceipt :
    SiblingEvidenceMissingReceipt

canonicalSiblingEvidenceMissingReceipts :
  List SiblingEvidenceMissingReceipt
canonicalSiblingEvidenceMissingReceipts =
  missingAcceptedDashiPredictionAPI
  ∷ missingCleanPredictionFreezeReceipt
  ∷ missingDigestBoundProjectionReceipt
  ∷ missingComparisonLawReceipt
  ∷ missingE8CarrierReceipt
  ∷ missingLamTungAdapterReceipt
  ∷ missingThetaJAgdaAdapterReceipt
  ∷ missingRuntimePNFReceipt
  ∷ missingProviderAuthorityReceipt
  ∷ []

data SiblingEvidencePromotedReceipt : Set where

siblingEvidencePromotionImpossibleHere :
  SiblingEvidencePromotedReceipt →
  ⊥
siblingEvidencePromotionImpossibleHere ()

record SiblingEvidenceInventory : Setω where
  field
    status :
      SiblingEvidenceInventoryStatus

    siblingEvidenceFound :
      Bool

    siblingEvidenceFoundIsTrue :
      siblingEvidenceFound ≡ true

    promotesAnyGate :
      Bool

    promotesAnyGateIsFalse :
      promotesAnyGate ≡ false

    evidenceKinds :
      List SiblingEvidenceKind

    evidenceKindsAreCanonical :
      evidenceKinds ≡ canonicalSiblingEvidenceKinds

    evidenceEntries :
      List SiblingEvidenceEntry

    evidenceEntriesAreCanonical :
      evidenceEntries ≡ canonicalSiblingEvidenceEntries

    missingReceipts :
      List SiblingEvidenceMissingReceipt

    missingReceiptsAreCanonical :
      missingReceipts ≡ canonicalSiblingEvidenceMissingReceipts

    inventoryNotes :
      List String

    nonPromotionBoundary :
      List String

    promotedReceiptBlocked :
      SiblingEvidencePromotedReceipt →
      ⊥

canonicalSiblingEvidenceInventory :
  SiblingEvidenceInventory
canonicalSiblingEvidenceInventory =
  record
    { status =
        siblingEvidenceFoundButReceiptsMissing
    ; siblingEvidenceFound =
        true
    ; siblingEvidenceFoundIsTrue =
        refl
    ; promotesAnyGate =
        false
    ; promotesAnyGateIsFalse =
        refl
    ; evidenceKinds =
        canonicalSiblingEvidenceKinds
    ; evidenceKindsAreCanonical =
        refl
    ; evidenceEntries =
        canonicalSiblingEvidenceEntries
    ; evidenceEntriesAreCanonical =
        refl
    ; missingReceipts =
        canonicalSiblingEvidenceMissingReceipts
    ; missingReceiptsAreCanonical =
        refl
    ; inventoryNotes =
        "Sibling evidence is useful for routing and cross-checking but is not a provider receipt"
        ∷ "dashifine/dashiQ/dashitest phi-star artifacts can guide the accepted DASHI prediction API route"
        ∷ "DASHIg LILA Phase 2 artifacts can guide the trace lane but not E8/Lam-Tung physics closure"
        ∷ "dashi_lean4 moonshine arithmetic can guide a future Agda theta/J adapter but is not imported here"
        ∷ []
    ; nonPromotionBoundary =
        "This inventory records read-only sibling evidence pointers"
        ∷ "It constructs no clean prediction freeze receipt"
        ∷ "It constructs no accepted DASHI phi-star prediction API"
        ∷ "It constructs no digest-bound projection artifact"
        ∷ "It constructs no comparison-law receipt"
        ∷ "It constructs no E8 carrier, Lam-Tung adapter, theta/J bridge, or phi-star projection receipt"
        ∷ "It constructs no W3/W4/W5/W6/W8/W9 promotion receipt"
        ∷ []
    ; promotedReceiptBlocked =
        siblingEvidencePromotionImpossibleHere
    }

canonicalSiblingEvidenceInventoryStatus :
  SiblingEvidenceInventoryStatus
canonicalSiblingEvidenceInventoryStatus =
  siblingEvidenceFoundButReceiptsMissing
