module DASHI.Physics.Closure.LilaE8RootSystemLocalSourceDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- LILA/E8 local source diagnostic.
--
-- This module inventories local and sibling-read-only evidence for a proposed
-- E8/Lam-Tung/phi-star projection lane.  It is a source-surface only: the
-- local files show bridge vocabulary, execution traces, E8/Leech tokenizer
-- artifacts, and phi-star HEPData projection surfaces, but they do not provide
-- an E8 root-system theorem, a Lam-Tung derivation, or a promoted physics
-- receipt.

data LilaE8RootSystemLocalSourceDiagnosticStatus : Set where
  localEvidenceFoundButProjectionReceiptMissing :
    LilaE8RootSystemLocalSourceDiagnosticStatus

data LilaE8LocalSourceKind : Set where
  dashiLilaBridgeDocument :
    LilaE8LocalSourceKind
  dashiLilaTraceSchema :
    LilaE8LocalSourceKind
  dashigPhase2ValidationNote :
    LilaE8LocalSourceKind
  dashigPhase2PipelineScript :
    LilaE8LocalSourceKind
  dashigLilaTraceArtifact :
    LilaE8LocalSourceKind
  dashigE8VocabularyArtifact :
    LilaE8LocalSourceKind
  dashigLeechBenchmarkSurface :
    LilaE8LocalSourceKind
  dashiPhiStarAuthoritySurface :
    LilaE8LocalSourceKind
  dashiPhiStarRatioArtifactReceipt :
    LilaE8LocalSourceKind
  dashiPhiStarProjectionRunnerContract :
    LilaE8LocalSourceKind
  dashifinePhiStarProjectionArtifact :
    LilaE8LocalSourceKind

canonicalLilaE8LocalSourceKinds :
  List LilaE8LocalSourceKind
canonicalLilaE8LocalSourceKinds =
  dashiLilaBridgeDocument
  ∷ dashiLilaTraceSchema
  ∷ dashigPhase2ValidationNote
  ∷ dashigPhase2PipelineScript
  ∷ dashigLilaTraceArtifact
  ∷ dashigE8VocabularyArtifact
  ∷ dashigLeechBenchmarkSurface
  ∷ dashiPhiStarAuthoritySurface
  ∷ dashiPhiStarRatioArtifactReceipt
  ∷ dashiPhiStarProjectionRunnerContract
  ∷ dashifinePhiStarProjectionArtifact
  ∷ []

record LilaE8LocalSourceEntry : Set where
  field
    sourceKind :
      LilaE8LocalSourceKind

    localPath :
      String

    evidenceRole :
      String

    promotionBoundary :
      String

canonicalLilaBridgeDocumentSource :
  LilaE8LocalSourceEntry
canonicalLilaBridgeDocumentSource =
  record
    { sourceKind =
        dashiLilaBridgeDocument
    ; localPath =
        "Docs/LILA_DASHI_Bridge.md"
    ; evidenceRole =
        "states LILA as execution system and DASHI as admissibility/receipt lens"
    ; promotionBoundary =
        "bridge contract only; not an equality claim and not an E8 physics theorem"
    }

canonicalLilaTraceSchemaSource :
  LilaE8LocalSourceEntry
canonicalLilaTraceSchemaSource =
  record
    { sourceKind =
        dashiLilaTraceSchema
    ; localPath =
        "DASHI/Physics/Closure/LilaTraceFamily.agda"
    ; evidenceRole =
        "typed row-to-receipt schema for LILA execution traces"
    ; promotionBoundary =
        "requires concrete ExecutionContract receipts; does not assert root-system physics"
    }

canonicalDashigPhase2ValidationNoteSource :
  LilaE8LocalSourceEntry
canonicalDashigPhase2ValidationNoteSource =
  record
    { sourceKind =
        dashigPhase2ValidationNote
    ; localPath =
        "../DASHIg/LILA_PHASE2_VALIDATION.md"
    ; evidenceRole =
        "external LILA/Leech logs are adapted onto the Phase 2 timing and delta-cone surface"
    ; promotionBoundary =
        "empirical comparison plane only; explicitly not proof that geometry enforces safety"
    }

canonicalDashigPhase2PipelineScriptSource :
  LilaE8LocalSourceEntry
canonicalDashigPhase2PipelineScriptSource =
  record
    { sourceKind =
        dashigPhase2PipelineScript
    ; localPath =
        "../DASHIg/35_lila_log_to_csv.py; ../DASHIg/36_lila_training_dynamics.py; ../DASHIg/37_lila_delta_cone_analysis.py; ../DASHIg/38_lila_phase2_pipeline.sh"
    ; evidenceRole =
        "local scripts adapt raw LILA logs, plot training dynamics, and rank delta-cone masks"
    ; promotionBoundary =
        "script evidence only; no accepted projection receipt or theorem token"
    }

canonicalDashigLilaTraceArtifactSource :
  LilaE8LocalSourceEntry
canonicalDashigLilaTraceArtifactSource =
  record
    { sourceKind =
        dashigLilaTraceArtifact
    ; localPath =
        "../DASHIg/lila_phase2_validation/lila_external.csv; ../DASHIg/lila_phase2_validation/lila_external_delta_cone.csv"
    ; evidenceRole =
        "sample adapted LILA trace rows from LeechTransformer/train_logs/340K.md plus delta-cone summary"
    ; promotionBoundary =
        "sample empirical trace artifact only; not an accepted DASHI execution-contract receipt"
    }

canonicalDashigE8VocabularyArtifactSource :
  LilaE8LocalSourceEntry
canonicalDashigE8VocabularyArtifactSource =
  record
    { sourceKind =
        dashigE8VocabularyArtifact
    ; localPath =
        "../DASHIg/LeechTransformer/vocab/e8_morpheme_.vocab; ../DASHIg/LeechTransformer/vocab/e8_morpheme_.model"
    ; evidenceRole =
        "local E8-named tokenizer/vocabulary artifact for LeechTransformer material"
    ; promotionBoundary =
        "vocabulary naming evidence only; no E8 lattice basis, Weyl action, or physics interpretation receipt"
    }

canonicalDashigLeechBenchmarkSurfaceSource :
  LilaE8LocalSourceEntry
canonicalDashigLeechBenchmarkSurfaceSource =
  record
    { sourceKind =
        dashigLeechBenchmarkSurface
    ; localPath =
        "../DASHIg/phase2_validation/leech_modular_benchmark.py; ../DASHIg/leech_vs_dashifine_seed0.csv; ../DASHIg/leech_vs_dashifine_seed0.md"
    ; evidenceRole =
        "translated Leech-vs-DASHI benchmark and comparison surface"
    ; promotionBoundary =
        "architecture comparison only; not evidence that E8 closes Lam-Tung or phi-star physics"
    }

canonicalDashiPhiStarAuthoritySurfaceSource :
  LilaE8LocalSourceEntry
canonicalDashiPhiStarAuthoritySurfaceSource =
  record
    { sourceKind =
        dashiPhiStarAuthoritySurface
    ; localPath =
        "DASHI/Physics/Closure/HEPDataEmpiricalAuthorityReceiptCollation.agda"
    ; evidenceRole =
        "binds CMS-SMP-20-003 / HEPData ins2079374 phi-star source and local normalized artifact context"
    ; promotionBoundary =
        "non-promoting authority collation; adapter-transform receipt still missing"
    }

canonicalDashiPhiStarRatioArtifactReceiptSource :
  LilaE8LocalSourceEntry
canonicalDashiPhiStarRatioArtifactReceiptSource =
  record
    { sourceKind =
        dashiPhiStarRatioArtifactReceipt
    ; localPath =
        "DASHI/Physics/Closure/HEPDataRatioTableArtifactReceipt.agda"
    ; evidenceRole =
        "checksum-binds t43/t44 dimensionless phi-star ratio CSV artifacts"
    ; promotionBoundary =
        "no CSV parsing, no projection run, no comparison law, no W3/W4/W5/W8 promotion"
    }

canonicalDashiPhiStarProjectionRunnerContractSource :
  LilaE8LocalSourceEntry
canonicalDashiPhiStarProjectionRunnerContractSource =
  record
    { sourceKind =
        dashiPhiStarProjectionRunnerContract
    ; localPath =
        "DASHI/Physics/Closure/HEPDataT43ProjectionRunnerContract.agda"
    ; evidenceRole =
        "names required inputs and outputs for a future digest-bound t43 projection runner"
    ; promotionBoundary =
        "contract skeleton only; current discovery says no accepted exact runner exists here"
    }

canonicalDashifinePhiStarProjectionArtifactSource :
  LilaE8LocalSourceEntry
canonicalDashifinePhiStarProjectionArtifactSource =
  record
    { sourceKind =
        dashifinePhiStarProjectionArtifact
    ; localPath =
        "../dashifine/hepdata_npz/phistar_50_76.npz; ../dashifine/hepdata_dashi_native/phistar_50_76_dashi_native_metrics.csv; ../dashifine/hepdata_to_dashi/phistar_50_76/"
    ; evidenceRole =
        "sibling phi-star lens/projection artifacts used as local evidence pointers"
    ; promotionBoundary =
        "read-only sibling artifacts; not an accepted in-repo projection receipt"
    }

canonicalLilaE8LocalSourceEntries :
  List LilaE8LocalSourceEntry
canonicalLilaE8LocalSourceEntries =
  canonicalLilaBridgeDocumentSource
  ∷ canonicalLilaTraceSchemaSource
  ∷ canonicalDashigPhase2ValidationNoteSource
  ∷ canonicalDashigPhase2PipelineScriptSource
  ∷ canonicalDashigLilaTraceArtifactSource
  ∷ canonicalDashigE8VocabularyArtifactSource
  ∷ canonicalDashigLeechBenchmarkSurfaceSource
  ∷ canonicalDashiPhiStarAuthoritySurfaceSource
  ∷ canonicalDashiPhiStarRatioArtifactReceiptSource
  ∷ canonicalDashiPhiStarProjectionRunnerContractSource
  ∷ canonicalDashifinePhiStarProjectionArtifactSource
  ∷ []

data LilaE8MissingLocalReceipt : Set where
  missingE8RootSystemCarrierReceipt :
    LilaE8MissingLocalReceipt
  missingE8RootCountAndInnerProductReceipt :
    LilaE8MissingLocalReceipt
  missingE8WeylActionOrProjectionReceipt :
    LilaE8MissingLocalReceipt
  missingLamTungObservableDefinitionReceipt :
    LilaE8MissingLocalReceipt
  missingPhiStarToLamTungAdapterReceipt :
    LilaE8MissingLocalReceipt
  missingPredictionFreezeReceipt :
    LilaE8MissingLocalReceipt
  missingDigestBoundProjectionRunReceipt :
    LilaE8MissingLocalReceipt
  missingComparisonLawReceipt :
    LilaE8MissingLocalReceipt
  missingAcceptedPhysicsAuthorityPromotionReceipt :
    LilaE8MissingLocalReceipt

canonicalLilaE8MissingLocalReceipts :
  List LilaE8MissingLocalReceipt
canonicalLilaE8MissingLocalReceipts =
  missingE8RootSystemCarrierReceipt
  ∷ missingE8RootCountAndInnerProductReceipt
  ∷ missingE8WeylActionOrProjectionReceipt
  ∷ missingLamTungObservableDefinitionReceipt
  ∷ missingPhiStarToLamTungAdapterReceipt
  ∷ missingPredictionFreezeReceipt
  ∷ missingDigestBoundProjectionRunReceipt
  ∷ missingComparisonLawReceipt
  ∷ missingAcceptedPhysicsAuthorityPromotionReceipt
  ∷ []

data LilaE8PromotedPhysicsReceipt : Set where

lilaE8PromotionImpossibleHere :
  LilaE8PromotedPhysicsReceipt →
  ⊥
lilaE8PromotionImpossibleHere ()

record LilaPhase2ValidationArtifactSummary : Set where
  field
    directory :
      String

    trainingCsv :
      String

    deltaConeCsv :
      String

    trainingPlot :
      String

    trainingRows :
      String

    trainingStepRange :
      String

    trainingColumns :
      String

    deltaConeRows :
      String

    deltaConeColumns :
      String

    firstDeltaConeRow :
      String

    secondDeltaConeRow :
      String

    evidenceRole :
      String

    promotionBoundary :
      String

canonicalLilaPhase2ValidationArtifactSummary :
  LilaPhase2ValidationArtifactSummary
canonicalLilaPhase2ValidationArtifactSummary =
  record
    { directory =
        "/home/c/Documents/code/DASHIg/lila_phase2_validation"
    ; trainingCsv =
        "lila_external.csv"
    ; deltaConeCsv =
        "lila_external_delta_cone.csv"
    ; trainingPlot =
        "lila_external_training_dynamics.png"
    ; trainingRows =
        "104"
    ; trainingStepRange =
        "330100..340400"
    ; trainingColumns =
        "model_name, source_log, step, train_loss, val_loss"
    ; deltaConeRows =
        "2"
    ; deltaConeColumns =
        "p, q, z, mask, cone_frac, forward_frac, forward_cone_frac_all, forward_cone_frac_conditional, n_steps, n_forward, n_cone, mean_Qd, min_Qd, max_Qd"
    ; firstDeltaConeRow =
        "p=0 q=1 z=0 mask=-1 n_steps=103 n_forward=49 n_cone=103 mean_Qd=-0.8597014377827848"
    ; secondDeltaConeRow =
        "p=1 q=0 z=0 mask=1 n_steps=103 n_forward=49 n_cone=29 mean_Qd=0.8597014377827848"
    ; evidenceRole =
        "concrete LILA Phase 2 execution-trace and delta-cone evidence pointer"
    ; promotionBoundary =
        "trace artifact summary only; not an E8 root enumeration, Lam-Tung adapter, theta/J bridge, phi-star projection, or DASHI empirical receipt"
    }

record LilaE8RootSystemLocalSourceDiagnostic : Setω where
  field
    status :
      LilaE8RootSystemLocalSourceDiagnosticStatus

    localSourcesFound :
      Bool

    localSourcesFoundIsTrue :
      localSourcesFound ≡ true

    e8PhysicsTheoremCompletedHere :
      Bool

    e8PhysicsTheoremCompletedHereIsFalse :
      e8PhysicsTheoremCompletedHere ≡ false

    sourceKinds :
      List LilaE8LocalSourceKind

    sourceKindsAreCanonical :
      sourceKinds ≡ canonicalLilaE8LocalSourceKinds

    sourceEntries :
      List LilaE8LocalSourceEntry

    sourceEntriesAreCanonical :
      sourceEntries ≡ canonicalLilaE8LocalSourceEntries

    missingReceipts :
      List LilaE8MissingLocalReceipt

    missingReceiptsAreCanonical :
      missingReceipts ≡ canonicalLilaE8MissingLocalReceipts

    inventoryNotes :
      List String

    phase2ValidationArtifactSummary :
      LilaPhase2ValidationArtifactSummary

    nonPromotionBoundary :
      List String

    promotedPhysicsReceiptBlocked :
      LilaE8PromotedPhysicsReceipt →
      ⊥

canonicalLilaE8RootSystemLocalSourceDiagnostic :
  LilaE8RootSystemLocalSourceDiagnostic
canonicalLilaE8RootSystemLocalSourceDiagnostic =
  record
    { status =
        localEvidenceFoundButProjectionReceiptMissing
    ; localSourcesFound =
        true
    ; localSourcesFoundIsTrue =
        refl
    ; e8PhysicsTheoremCompletedHere =
        false
    ; e8PhysicsTheoremCompletedHereIsFalse =
        refl
    ; sourceKinds =
        canonicalLilaE8LocalSourceKinds
    ; sourceKindsAreCanonical =
        refl
    ; sourceEntries =
        canonicalLilaE8LocalSourceEntries
    ; sourceEntriesAreCanonical =
        refl
    ; missingReceipts =
        canonicalLilaE8MissingLocalReceipts
    ; missingReceiptsAreCanonical =
        refl
    ; inventoryNotes =
        "Local LILA bridge material exists in Docs/LILA_DASHI_Bridge.md and DASHI/Physics/Closure/LilaTraceFamily.agda"
        ∷ "Sibling ../DASHIg contains LILA Phase 2 scripts, an adapted LeechTransformer 340K trace, delta-cone output, and E8-named tokenizer files"
        ∷ "The inspected Phase 2 validation directory has lila_external.csv with 104 rows over steps 330100..340400, lila_external_delta_cone.csv with 2 summary rows over 103 steps, and a 1760x960 PNG training-dynamics plot"
        ∷ "Sibling ../dashifine and in-repo HEPData modules contain phi-star source and projection-lane artifacts"
        ∷ "No local source inspected here supplies a Lam-Tung derivation from E8 or a completed E8 root-system projection theorem"
        ∷ []
    ; phase2ValidationArtifactSummary =
        canonicalLilaPhase2ValidationArtifactSummary
    ; nonPromotionBoundary =
        "This diagnostic inventories local evidence only"
        ∷ "It does not parse or certify sibling artifacts"
        ∷ "The Phase 2 validation artifacts are execution-trace evidence only, not E8/Lam-Tung/phi-star receipts"
        ∷ "It does not assert an E8 root-system carrier, root count, inner product, Weyl action, or projection law"
        ∷ "It does not assert Lam-Tung closure or phi-star agreement"
        ∷ "It does not promote any physics theorem"
        ∷ []
    ; promotedPhysicsReceiptBlocked =
        lilaE8PromotionImpossibleHere
    }

canonicalLilaE8LocalSourcesFound :
  Bool
canonicalLilaE8LocalSourcesFound =
  LilaE8RootSystemLocalSourceDiagnostic.localSourcesFound
    canonicalLilaE8RootSystemLocalSourceDiagnostic
