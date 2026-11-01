module DASHI.Physics.Closure.ExternalFormalImportRoadmapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- External formal import roadmap.
--
-- This module records import candidates that may compress the GR/QFT
-- roadmap.  It does not import the external libraries and does not claim that
-- their theorems have been consumed by DASHI.  Promotion requires vendoring or
-- otherwise making the dependency available to Agda, typechecking the bridge,
-- and then replacing the candidate status below with an imported receipt.

data ExternalFormalImportCandidate : Set where
  dchottAgda :
    ExternalFormalImportCandidate

  haagKastlerStacks :
    ExternalFormalImportCandidate

  schreiberCohesiveHoTT :
    ExternalFormalImportCandidate

data ExternalImportStageTarget : Set where
  metricAdapterStage :
    ExternalImportStageTarget

  aqftCarrierStage :
    ExternalImportStageTarget

  grqftAmbientFrameworkStage :
    ExternalImportStageTarget

data ExternalImportStatus : Set where
  externalCandidateVerified :
    ExternalImportStatus

  localDependencyMissing :
    ExternalImportStatus

  dependencyIntakeShimTypechecked :
    ExternalImportStatus

  bridgeSocketTypechecked :
    ExternalImportStatus

  dashNativeReceiptTypechecked :
    ExternalImportStatus

  importedAndTypechecked :
    ExternalImportStatus

record ExternalFormalImportCandidateReceipt : Setω where
  field
    candidate :
      ExternalFormalImportCandidate

    stageTarget :
      ExternalImportStageTarget

    status :
      ExternalImportStatus

    sourceName :
      String

    sourceLocator :
      String

    toolchainCompatibility :
      String

    localDependencyPresent :
      Bool

    dashImportImplemented :
      Bool

    theoremImportedIntoDASHI :
      Bool

    leapfrogMechanism :
      String

    targetDASHIReceipt :
      String

    integrationObligations :
      List String

    governanceBoundary :
      List String

record LocalFormalOverlapAuditReceipt : Setω where
  field
    localFlatLeviCivitaSurfacePresent :
      Bool

    localFlatLeviCivitaSurfacePresentIsTrue :
      localFlatLeviCivitaSurfacePresent ≡ true

    localNonFlatLeviCivitaAdapterPresent :
      Bool

    localNonFlatLeviCivitaAdapterPresentIsFalse :
      localNonFlatLeviCivitaAdapterPresent ≡ false

    localGRQFTConsumerObligationPresent :
      Bool

    localGRQFTConsumerObligationPresentIsTrue :
      localGRQFTConsumerObligationPresent ≡ true

    localAQFTNetReceiptPresent :
      Bool

    localAQFTNetReceiptPresentIsTrue :
      localAQFTNetReceiptPresent ≡ true

    localKleinGordonAQFTReceiptPresent :
      Bool

    localKleinGordonAQFTReceiptPresentIsTrue :
      localKleinGordonAQFTReceiptPresent ≡ true

    localInteractingQFTBoundaryReceiptPresent :
      Bool

    localInteractingQFTBoundaryReceiptPresentIsTrue :
      localInteractingQFTBoundaryReceiptPresent ≡ true

    localAdapterBoundaryMatrixPresent :
      Bool

    localAdapterBoundaryMatrixPresentIsTrue :
      localAdapterBoundaryMatrixPresent ≡ true

    localDCHoTTDependencyPresent :
      Bool

    localDCHoTTDependencyPresentIsTrue :
      localDCHoTTDependencyPresent ≡ true

    localDCHoTTImportShimPresent :
      Bool

    localDCHoTTImportShimPresentIsTrue :
      localDCHoTTImportShimPresent ≡ true

    localDCHoTTLeviCivitaBridgePresent :
      Bool

    localDCHoTTLeviCivitaBridgePresentIsTrue :
      localDCHoTTLeviCivitaBridgePresent ≡ true

    localCohesiveBridgeTheoremPresent :
      Bool

    localCohesiveBridgeTheoremPresentIsFalse :
      localCohesiveBridgeTheoremPresent ≡ false

    strongestReading :
      String

    overlapEvidence :
      List String

    governanceBoundary :
      List String

record CompressedGRQFTImportRoadmapReceipt : Setω where
  field
    dchottMetricAdapter :
      ExternalFormalImportCandidateReceipt

    aqftNetCarrier :
      ExternalFormalImportCandidateReceipt

    cohesiveAmbientFramework :
      ExternalFormalImportCandidateReceipt

    localOverlapAudit :
      LocalFormalOverlapAuditReceipt

    stage2TimelineCompressed :
      Bool

    stage2TimelineCompressedIsTrue :
      stage2TimelineCompressed ≡ true

    stage3TimelineCompressed :
      Bool

    stage3TimelineCompressedIsTrue :
      stage3TimelineCompressed ≡ true

    stage4to6TimelineCompressed :
      Bool

    stage4to6TimelineCompressedIsTrue :
      stage4to6TimelineCompressed ≡ true

    importsCurrentlyTypecheckedInDASHI :
      Bool

    importsCurrentlyTypecheckedInDASHIIsTrue :
      importsCurrentlyTypecheckedInDASHI ≡ true

    noGRQFTPromotionFromThisReceipt :
      Bool

    noGRQFTPromotionFromThisReceiptIsTrue :
      noGRQFTPromotionFromThisReceipt ≡ true

    nextExecutableSteps :
      List String

    compressedRoadmapBoundary :
      List String

open ExternalFormalImportCandidateReceipt public
open LocalFormalOverlapAuditReceipt public
open CompressedGRQFTImportRoadmapReceipt public

canonicalDCHoTTMetricAdapterImportCandidate :
  ExternalFormalImportCandidateReceipt
canonicalDCHoTTMetricAdapterImportCandidate =
  record
    { candidate =
        dchottAgda
    ; stageTarget =
        metricAdapterStage
    ; status =
        bridgeSocketTypechecked
    ; sourceName =
        "DCHoTT-Agda / Wellen-Cherubini differential cohesion in Agda"
    ; sourceLocator =
        "https://github.com/felixwellen/DCHoTT-Agda ; Wellen thesis on formalizing Cartan geometry in modal HoTT"
    ; toolchainCompatibility =
        "DCHoTT-Agda README target Agda 2.6.2.2; DASHI flat import shim typechecks under Agda 2.6.4.3 with standard-library-2.0"
    ; localDependencyPresent =
        true
    ; dashImportImplemented =
        true
    ; theoremImportedIntoDASHI =
        false
    ; leapfrogMechanism =
        "use formal disk bundle, frame bundle, Cartan geometry, and torsion-free G-structure surfaces as candidate infrastructure for the metric adapter"
    ; targetDASHIReceipt =
        "LeviCivitaAdapterReceipt"
    ; integrationObligations =
        "record exact DCHoTT-Agda commit, license, Agda version, stdlib version, and compatibility notes"
        ∷ "replace LeviCivitaBridge's postulated B0-geometricEmergence socket with a proof or imported theorem"
        ∷ "identify the exact DCHoTT construction corresponding to the torsion-free G-structure / Levi-Civita adapter target"
        ∷ "write a translation layer from DASHI carrier/transport receipts into the DCHoTT modality vocabulary"
        ∷ "prove or import the specialisation from torsion-free G-structure to the DASHI Levi-Civita adapter target"
        ∷ []
    ; governanceBoundary =
        "DCHoTT dependency is local, the flat import shim typechecks, and LeviCivitaBridge typechecks against the actual G-structures socket"
        ∷ "no DCHoTT theorem is imported into a DASHI metric adapter by this roadmap receipt"
        ∷ "LeviCivitaBridge records B0 as a postulated open obligation and does not import torsion-free or Levi-Civita uniqueness"
        ∷ "Stage 2 is timeline-compressed by an existing formalisation candidate and import shim, not locally closed"
        ∷ "no metric adapter, Hodge star, Ricci contraction, Einstein tensor, or GR promotion follows from this receipt"
        ∷ []
    }

canonicalAQFTNetImportCandidate :
  ExternalFormalImportCandidateReceipt
canonicalAQFTNetImportCandidate =
  record
    { candidate =
        haagKastlerStacks
    ; stageTarget =
        aqftCarrierStage
    ; status =
        dashNativeReceiptTypechecked
    ; sourceName =
        "Haag-Kastler stacks"
    ; sourceLocator =
        "arXiv:2404.14510"
    ; toolchainCompatibility =
        "DASHI-native stdlib-only receipt; no external Agda AQFT dependency imported"
    ; localDependencyPresent =
        false
    ; dashImportImplemented =
        true
    ; theoremImportedIntoDASHI =
        false
    ; leapfrogMechanism =
        "replace single global Fock-space carrier with a local algebra net / Haag-Kastler 2-functor and descent conditions"
    ; targetDASHIReceipt =
        "AQFTNetReceipt"
    ; integrationObligations =
        "refine the bool/string receipt into typed OpenRegion, local algebra, isotony, causality, and time-slice carriers"
        ∷ "bind the local-to-global descent condition without selecting a Hilbert representation"
        ∷ "replace KleinGordonAQFTReceipt's cited theorem surface with a typed local algebra net if a proof-grade Agda AQFT library becomes available"
        ∷ "keep GNS state, vacuum selection, Born rule, and empirical representation choice as explicit adapters"
        ∷ "connect the AQFT net receipt to existing GRQFT consumer request-pack fields"
        ∷ []
    ; governanceBoundary =
        "DASHI.Physics.Closure.AQFTNetReceipt now records the Haag-Kastler point/descent contract"
        ∷ "DASHI.Physics.Closure.KleinGordonAQFTReceipt records the cited free-field stack witness"
        ∷ "DASHI.Physics.Closure.InteractingQFTBoundaryReceipt names constructive interacting nets as the first open QFT obligation"
        ∷ "AQFT nets avoid a premature single-Fock-space assumption but do not solve interacting QFT"
        ∷ "Haag theorem is staged around, not refuted"
        ∷ "no Born-rule, vacuum-selection, empirical QFT, or GRQFT promotion follows from this receipt"
        ∷ []
    }

canonicalCohesiveAmbientImportCandidate :
  ExternalFormalImportCandidateReceipt
canonicalCohesiveAmbientImportCandidate =
  record
    { candidate =
        schreiberCohesiveHoTT
    ; stageTarget =
        grqftAmbientFrameworkStage
    ; status =
        externalCandidateVerified
    ; sourceName =
        "Schreiber modal/cohesive HoTT physics programme"
    ; sourceLocator =
        "https://ncatlab.org/schreiber/show/Modern+Physics+formalized+in+Modal+Homotopy+Type+Theory"
    ; toolchainCompatibility =
        "conceptual ambient-framework candidate only; no local Agda dependency imported"
    ; localDependencyPresent =
        false
    ; dashImportImplemented =
        false
    ; theoremImportedIntoDASHI =
        false
    ; leapfrogMechanism =
        "use cohesive/modal HoTT as the ambient grammar in which carrier transport, metric adapters, gauge fields, and AQFT locality can be compared"
    ; targetDASHIReceipt =
        "GRQFTUnificationReceipt"
    ; integrationObligations =
        "map DASHI carrier, transport receipt, curvature receipt, admissibility, and promotion gates into the cohesive/modal vocabulary"
        ∷ "show how DCHoTT metric-adapter surfaces and AQFT net surfaces compose without changing ambient type theory"
        ∷ "name mass gap, cosmological constant, Born rule, and coupling calibration as explicit open obligations"
        ∷ []
    ; governanceBoundary =
        "ambient framework candidate only; no cohesive HoTT dependency is currently imported by DASHI"
        ∷ "this receipt compresses the roadmap but does not close Stage 4, Stage 5, Stage 6, or a TOE claim"
        ∷ "the honest claim remains typed staging of obligations, not structural derivation of empirical adapters"
        ∷ []
    }

canonicalLocalFormalOverlapAuditReceipt :
  LocalFormalOverlapAuditReceipt
canonicalLocalFormalOverlapAuditReceipt =
  record
    { localFlatLeviCivitaSurfacePresent =
        true
    ; localFlatLeviCivitaSurfacePresentIsTrue =
        refl
    ; localNonFlatLeviCivitaAdapterPresent =
        false
    ; localNonFlatLeviCivitaAdapterPresentIsFalse =
        refl
    ; localGRQFTConsumerObligationPresent =
        true
    ; localGRQFTConsumerObligationPresentIsTrue =
        refl
    ; localAQFTNetReceiptPresent =
        true
    ; localAQFTNetReceiptPresentIsTrue =
        refl
    ; localKleinGordonAQFTReceiptPresent =
        true
    ; localKleinGordonAQFTReceiptPresentIsTrue =
        refl
    ; localInteractingQFTBoundaryReceiptPresent =
        true
    ; localInteractingQFTBoundaryReceiptPresentIsTrue =
        refl
    ; localAdapterBoundaryMatrixPresent =
        true
    ; localAdapterBoundaryMatrixPresentIsTrue =
        refl
    ; localDCHoTTDependencyPresent =
        true
    ; localDCHoTTDependencyPresentIsTrue =
        refl
    ; localDCHoTTImportShimPresent =
        true
    ; localDCHoTTImportShimPresentIsTrue =
        refl
    ; localDCHoTTLeviCivitaBridgePresent =
        true
    ; localDCHoTTLeviCivitaBridgePresentIsTrue =
        refl
    ; localCohesiveBridgeTheoremPresent =
        false
    ; localCohesiveBridgeTheoremPresentIsFalse =
        refl
    ; strongestReading =
        "DASHI already has local overlap surfaces for flat Levi-Civita, GR/QFT consumer obligations, adapter-boundary governance, a DCHoTT flat import shim, a DCHoTT G-structures bridge socket, an AQFT net receipt, a Klein-Gordon free-field witness, and an interacting-QFT boundary receipt, but it does not yet import a torsion-free Levi-Civita adapter, refine AQFT into concrete algebra carriers, construct interacting QFT, or prove the cohesive bridge theorem"
    ; overlapEvidence =
        "DASHI.Physics.Closure.GRConcreteLeviCivita closes only the selected flat Minkowski Levi-Civita prerequisite"
        ∷ "DASHI.Physics.Closure.GRDiscreteBianchiFiniteR and DiscreteBianchiIdentitySurface name non-flat Riemann, Ricci, Bianchi, and Einstein adapter requests"
        ∷ "DASHI.Physics.Closure.GRQFTConsumerNextObligation names downstream GR/QFT closure fields and keeps promotion constructorless"
        ∷ "Docs/PhysicsLaneMaturityMatrix.md records local observable-net, GNS/vacuum, Born-rule, metric, representation, and calibration boundaries"
        ∷ "DASHI.Geometry.DCHoTTImportShim imports DCHoTT flat modules and exposes manifold, formal-disk, and G-structure sockets"
        ∷ "DASHI.Geometry.LeviCivitaBridge typechecks a non-promoting bridge against the actual DCHoTT G-structures socket and records B0 as first open obligation"
        ∷ "DASHI.Physics.Closure.AQFTNetReceipt records the Haag-Kastler point/descent contract without constructing a QFT representation"
        ∷ "DASHI.Physics.Closure.KleinGordonAQFTReceipt records the free-field Theorem 4.41 witness while keeping vacuum and Born-rule adapters open"
        ∷ "DASHI.Physics.Closure.InteractingQFTBoundaryReceipt records constructive interacting nets as first open QFT obligation"
        ∷ []
    ; governanceBoundary =
        "in-repo overlap and DCHoTT import resolution reduce translation work but do not satisfy imported-theorem gates"
        ∷ "flat Levi-Civita is not the non-flat metric adapter needed for GR promotion"
        ∷ "the AQFT/Klein-Gordon receipts are not concrete C*-algebra net reconstructions, GNS/vacuum derivations, Born-rule derivations, or interacting QFT proofs"
        ∷ "DCHoTT import shim and LeviCivitaBridge are not a torsion-free G-structure specialisation or B0 proof"
        ∷ "adapter-boundary prose is not the B0 geometric-emergence theorem"
        ∷ []
    }

canonicalCompressedGRQFTImportRoadmapReceipt :
  CompressedGRQFTImportRoadmapReceipt
canonicalCompressedGRQFTImportRoadmapReceipt =
  record
    { dchottMetricAdapter =
        canonicalDCHoTTMetricAdapterImportCandidate
    ; aqftNetCarrier =
        canonicalAQFTNetImportCandidate
    ; cohesiveAmbientFramework =
        canonicalCohesiveAmbientImportCandidate
    ; localOverlapAudit =
        canonicalLocalFormalOverlapAuditReceipt
    ; stage2TimelineCompressed =
        true
    ; stage2TimelineCompressedIsTrue =
        refl
    ; stage3TimelineCompressed =
        true
    ; stage3TimelineCompressedIsTrue =
        refl
    ; stage4to6TimelineCompressed =
        true
    ; stage4to6TimelineCompressedIsTrue =
        refl
    ; importsCurrentlyTypecheckedInDASHI =
        true
    ; importsCurrentlyTypecheckedInDASHIIsTrue =
        refl
    ; noGRQFTPromotionFromThisReceipt =
        true
    ; noGRQFTPromotionFromThisReceiptIsTrue =
        refl
    ; nextExecutableSteps =
        "record exact DCHoTT-Agda commit/hash/license and Agda/std-lib compatibility notes"
        ∷ "replace LeviCivitaBridge's B0 postulate with a proof/import and then refine it toward torsion-free/Levi-Civita uniqueness"
        ∷ "refine AQFTNetReceipt and KleinGordonAQFTReceipt from bool/string governance surfaces into typed OpenRegion/local-algebra/descent carriers before any QFT carrier promotion"
        ∷ "connect both bridges to GRQFTConsumerNextObligation without constructing GRQFTClosurePromotionReceipt"
        ∷ []
    ; compressedRoadmapBoundary =
        "existing external formal work compresses the roadmap only after dependency intake and bridge typechecking"
        ∷ "DASHI must not replace an open obligation with a citation; every imported theorem still needs a receipt boundary"
        ∷ "Paper 2 target is the translation layer, not a completed GRQFT or TOE theorem"
        ∷ []
    }
