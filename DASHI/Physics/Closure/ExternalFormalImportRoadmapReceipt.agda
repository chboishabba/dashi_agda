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

    localAQFTNetReceiptPresentIsFalse :
      localAQFTNetReceiptPresent ≡ false

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
        dependencyIntakeShimTypechecked
    ; sourceName =
        "DCHoTT-Agda / Wellen-Cherubini differential cohesion in Agda"
    ; sourceLocator =
        "https://github.com/felixwellen/DCHoTT-Agda ; Wellen thesis on formalizing Cartan geometry in modal HoTT"
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
        ∷ "extend the flat import shim into a typed DASHI-to-DCHoTT translation layer"
        ∷ "identify the exact DCHoTT construction corresponding to the torsion-free G-structure / Levi-Civita adapter target"
        ∷ "write a translation layer from DASHI carrier/transport receipts into the DCHoTT modality vocabulary"
        ∷ "prove or import the specialisation from torsion-free G-structure to the DASHI Levi-Civita adapter target"
        ∷ []
    ; governanceBoundary =
        "DCHoTT dependency is local and the flat import shim typechecks"
        ∷ "no DCHoTT theorem is imported into a DASHI metric adapter by this roadmap receipt"
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
        externalCandidateVerified
    ; sourceName =
        "Haag-Kastler stacks"
    ; sourceLocator =
        "arXiv:2404.14510"
    ; localDependencyPresent =
        false
    ; dashImportImplemented =
        false
    ; theoremImportedIntoDASHI =
        false
    ; leapfrogMechanism =
        "replace single global Fock-space carrier with a local algebra net / Haag-Kastler 2-functor and descent conditions"
    ; targetDASHIReceipt =
        "AQFTNetReceipt"
    ; integrationObligations =
        "define DASHI OpenRegion, local algebra, isotony, causality, and time-slice receipt surfaces"
        ∷ "bind the local-to-global descent condition without selecting a Hilbert representation"
        ∷ "keep GNS state, vacuum selection, Born rule, and empirical representation choice as explicit adapters"
        ∷ "connect the AQFT net receipt to existing GRQFT consumer request-pack fields"
        ∷ []
    ; governanceBoundary =
        "AQFT nets avoid a premature single-Fock-space assumption but do not solve interacting QFT"
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
        false
    ; localAQFTNetReceiptPresentIsFalse =
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
    ; localCohesiveBridgeTheoremPresent =
        false
    ; localCohesiveBridgeTheoremPresentIsFalse =
        refl
    ; strongestReading =
        "DASHI already has local overlap surfaces for flat Levi-Civita, GR/QFT consumer obligations, adapter-boundary governance, and a DCHoTT flat import shim, but it does not yet import a torsion-free Levi-Civita adapter, define an AQFT net receipt, or prove the cohesive bridge theorem"
    ; overlapEvidence =
        "DASHI.Physics.Closure.GRConcreteLeviCivita closes only the selected flat Minkowski Levi-Civita prerequisite"
        ∷ "DASHI.Physics.Closure.GRDiscreteBianchiFiniteR and DiscreteBianchiIdentitySurface name non-flat Riemann, Ricci, Bianchi, and Einstein adapter requests"
        ∷ "DASHI.Physics.Closure.GRQFTConsumerNextObligation names downstream GR/QFT closure fields and keeps promotion constructorless"
        ∷ "Docs/PhysicsLaneMaturityMatrix.md records local observable-net, GNS/vacuum, Born-rule, metric, representation, and calibration boundaries"
        ∷ "DASHI.Geometry.DCHoTTImportShim imports DCHoTT flat modules and exposes manifold, formal-disk, and G-structure sockets"
        ∷ []
    ; governanceBoundary =
        "in-repo overlap and DCHoTT import resolution reduce translation work but do not satisfy imported-theorem gates"
        ∷ "flat Levi-Civita is not the non-flat metric adapter needed for GR promotion"
        ∷ "GRQFT consumer obligations are not Haag-Kastler AQFT nets"
        ∷ "DCHoTT import shim is not a torsion-free G-structure specialisation or B0 proof"
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
        ∷ "extend the DCHoTT import shim into a typed translation layer before writing the Levi-Civita adapter bridge"
        ∷ "add AQFTNetReceipt as a DASHI-native net/descent interface before any QFT carrier promotion"
        ∷ "connect both bridges to GRQFTConsumerNextObligation without constructing GRQFTClosurePromotionReceipt"
        ∷ []
    ; compressedRoadmapBoundary =
        "existing external formal work compresses the roadmap only after dependency intake and bridge typechecking"
        ∷ "DASHI must not replace an open obligation with a citation; every imported theorem still needs a receipt boundary"
        ∷ "Paper 2 target is the translation layer, not a completed GRQFT or TOE theorem"
        ∷ []
    }
