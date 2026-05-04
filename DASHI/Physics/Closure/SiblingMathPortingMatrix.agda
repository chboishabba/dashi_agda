module DASHI.Physics.Closure.SiblingMathPortingMatrix where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- SIB-MATRIX: sibling math porting coordination surface.
--
-- This module classifies sibling-repo artifacts for possible Agda porting.
-- It is deliberately non-promoting: no row here constructs a gate receipt,
-- imports external authority, or rebinds a DASHI-native closure obligation.
-- Diagrams should add a SIB-MATRIX node pointing at this surface, but this
-- module intentionally performs no diagram or P0 index edit.

data SiblingMathPortingMatrixStatus : Set where
  siblingPortMatrixRecordedNoPromotion :
    SiblingMathPortingMatrixStatus

data SiblingArtifactKind : Set where
  dashifineContractionCertificate :
    SiblingArtifactKind
  dashifineLyapunovEnergy :
    SiblingArtifactKind
  fejerClosestPoint :
    SiblingArtifactKind
  signatureSurface :
    SiblingArtifactKind
  coneOrbitProfile :
    SiblingArtifactKind
  hepDataLensProjection :
    SiblingArtifactKind
  seamCertificate :
    SiblingArtifactKind
  base369LogicTlureyOverflow :
    SiblingArtifactKind
  gpuIrPrimitives :
    SiblingArtifactKind
  leanMoonshineArithmetic :
    SiblingArtifactKind
  e8VocabTokenizer :
    SiblingArtifactKind
  lilaTrainingDynamics :
    SiblingArtifactKind
  quantumCurvatureExperiments :
    SiblingArtifactKind
  tradingVulkanCodec :
    SiblingArtifactKind

canonicalSiblingArtifactKinds :
  List SiblingArtifactKind
canonicalSiblingArtifactKinds =
  dashifineContractionCertificate
  ∷ dashifineLyapunovEnergy
  ∷ fejerClosestPoint
  ∷ signatureSurface
  ∷ coneOrbitProfile
  ∷ hepDataLensProjection
  ∷ seamCertificate
  ∷ base369LogicTlureyOverflow
  ∷ gpuIrPrimitives
  ∷ leanMoonshineArithmetic
  ∷ e8VocabTokenizer
  ∷ lilaTrainingDynamics
  ∷ quantumCurvatureExperiments
  ∷ tradingVulkanCodec
  ∷ []

data PortingDisposition : Set where
  portToAgda :
    PortingDisposition
  portToAgdaProjectionCandidate :
    PortingDisposition
  citationOnly :
    PortingDisposition
  diagnosticOnly :
    PortingDisposition
  ignoreForClosure :
    PortingDisposition

data TargetLane : Set where
  W1 :
    TargetLane
  W2 :
    TargetLane
  W3 :
    TargetLane
  W5 :
    TargetLane
  W6 :
    TargetLane
  W9 :
    TargetLane
  G1 :
    TargetLane
  G6 :
    TargetLane
  LILA-R1 :
    TargetLane
  LILA-R4 :
    TargetLane

data PortPriority : Set where
  portPriority1 :
    PortPriority
  portPriority2 :
    PortPriority
  portPriority3 :
    PortPriority
  noPortPriority :
    PortPriority
  ignoredPriority :
    PortPriority

canonicalPriorityStack :
  List String
canonicalPriorityStack =
  "Port 1: direct closure math certificates and seam material that can become DASHI-native W1/W2/W9 surfaces after reproof"
  ∷ "Port 2: signature, cone, orbit, and projection surfaces that help route G1/G6/W3/W9 work without promotion"
  ∷ "Port 3: citation and diagnostic support retained as evidence pointers only, not closure receipts"
  ∷ []

record SiblingPortMatrixEntry : Set where
  field
    artifactKind :
      SiblingArtifactKind

    artifactLabel :
      String

    disposition :
      PortingDisposition

    targetLanes :
      List TargetLane

    priority :
      PortPriority

    triage :
      String

    acceptanceBoundary :
      String

    promotionBoundary :
      String

dashifineContractionCertificateEntry :
  SiblingPortMatrixEntry
dashifineContractionCertificateEntry =
  record
    { artifactKind =
        dashifineContractionCertificate
    ; artifactLabel =
        "dashifine contraction certificate"
    ; disposition =
        portToAgda
    ; targetLanes =
        W2 ∷ W9 ∷ []
    ; priority =
        portPriority1
    ; triage =
        "port-to-Agda W2/W9"
    ; acceptanceBoundary =
        "Reprove inside DASHI Agda before use; sibling certificate is route input only"
    ; promotionBoundary =
        "No W2 or W9 promotion follows from this classification row"
    }

dashifineLyapunovEnergyEntry :
  SiblingPortMatrixEntry
dashifineLyapunovEnergyEntry =
  record
    { artifactKind =
        dashifineLyapunovEnergy
    ; artifactLabel =
        "dashifine Lyapunov/energy"
    ; disposition =
        portToAgda
    ; targetLanes =
        W2 ∷ W9 ∷ []
    ; priority =
        portPriority1
    ; triage =
        "port-to-Agda W2/W9"
    ; acceptanceBoundary =
        "Port only after binding the DASHI carrier state and energy functional in-repo"
    ; promotionBoundary =
        "No W2 or W9 gate is promoted by the sibling summary"
    }

fejerClosestPointEntry :
  SiblingPortMatrixEntry
fejerClosestPointEntry =
  record
    { artifactKind =
        fejerClosestPoint
    ; artifactLabel =
        "Fejer/closest-point"
    ; disposition =
        portToAgda
    ; targetLanes =
        W2 ∷ []
    ; priority =
        portPriority1
    ; triage =
        "port-to-Agda W2"
    ; acceptanceBoundary =
        "Translate as DASHI-native Fejer and closest-point lemmas before any closure use"
    ; promotionBoundary =
        "No W2 promotion is constructed here"
    }

signatureSurfaceEntry :
  SiblingPortMatrixEntry
signatureSurfaceEntry =
  record
    { artifactKind =
        signatureSurface
    ; artifactLabel =
        "signature surface"
    ; disposition =
        portToAgda
    ; targetLanes =
        G1 ∷ G6 ∷ []
    ; priority =
        portPriority2
    ; triage =
        "port-to-Agda G1/G6"
    ; acceptanceBoundary =
        "Port as a typed signature surface only after aligning with DASHI gauge and signature vocabulary"
    ; promotionBoundary =
        "No G1 or G6 gate is promoted by this matrix"
    }

coneOrbitProfileEntry :
  SiblingPortMatrixEntry
coneOrbitProfileEntry =
  record
    { artifactKind =
        coneOrbitProfile
    ; artifactLabel =
        "cone/orbit profile"
    ; disposition =
        portToAgda
    ; targetLanes =
        W9 ∷ []
    ; priority =
        portPriority2
    ; triage =
        "port-to-Agda W9"
    ; acceptanceBoundary =
        "Port only as a DASHI-native profile with explicit orbit and cone semantics"
    ; promotionBoundary =
        "No W9 pressure or orbit acceptance is constructed here"
    }

hepDataLensProjectionEntry :
  SiblingPortMatrixEntry
hepDataLensProjectionEntry =
  record
    { artifactKind =
        hepDataLensProjection
    ; artifactLabel =
        "HEPData lens/projection"
    ; disposition =
        portToAgdaProjectionCandidate
    ; targetLanes =
        W3 ∷ []
    ; priority =
        portPriority2
    ; triage =
        "port-to-Agda W3; projection-candidate only until DASHI-native sigma"
    ; acceptanceBoundary =
        "Projection candidate only until sigma_DASHI is constructed in DASHI-native Agda/API form"
    ; promotionBoundary =
        "No W3 empirical target or provider authority is promoted"
    }

seamCertificateEntry :
  SiblingPortMatrixEntry
seamCertificateEntry =
  record
    { artifactKind =
        seamCertificate
    ; artifactLabel =
        "seam certificate"
    ; disposition =
        portToAgda
    ; targetLanes =
        W1 ∷ []
    ; priority =
        portPriority1
    ; triage =
        "port-to-Agda W1"
    ; acceptanceBoundary =
        "Port as an internal seam certificate and bind it to the existing DASHI closure vocabulary"
    ; promotionBoundary =
        "No W1 seam promotion follows from the sibling classification"
    }

base369LogicTlureyOverflowEntry :
  SiblingPortMatrixEntry
base369LogicTlureyOverflowEntry =
  record
    { artifactKind =
        base369LogicTlureyOverflow
    ; artifactLabel =
        "Base369/LogicTlurey/overflow"
    ; disposition =
        citationOnly
    ; targetLanes =
        G1 ∷ []
    ; priority =
        portPriority3
    ; triage =
        "citation-only G1"
    ; acceptanceBoundary =
        "May be cited as background for G1 routing; not a porting receipt"
    ; promotionBoundary =
        "No G1 promotion or overflow authority is accepted"
    }

gpuIrPrimitivesEntry :
  SiblingPortMatrixEntry
gpuIrPrimitivesEntry =
  record
    { artifactKind =
        gpuIrPrimitives
    ; artifactLabel =
        "GPU/IR primitives"
    ; disposition =
        diagnosticOnly
    ; targetLanes =
        []
    ; priority =
        noPortPriority
    ; triage =
        "diagnostic-only"
    ; acceptanceBoundary =
        "Runtime and IR diagnostics only; not a closure math port"
    ; promotionBoundary =
        "No gate or runtime authority is promoted"
    }

leanMoonshineArithmeticEntry :
  SiblingPortMatrixEntry
leanMoonshineArithmeticEntry =
  record
    { artifactKind =
        leanMoonshineArithmetic
    ; artifactLabel =
        "Lean moonshine arithmetic"
    ; disposition =
        citationOnly
    ; targetLanes =
        LILA-R4 ∷ []
    ; priority =
        portPriority3
    ; triage =
        "citation-only LILA-R4"
    ; acceptanceBoundary =
        "Can guide a future Agda theta/J adapter but is not imported as a theorem"
    ; promotionBoundary =
        "No LILA-R4 theta/J receipt is promoted"
    }

e8VocabTokenizerEntry :
  SiblingPortMatrixEntry
e8VocabTokenizerEntry =
  record
    { artifactKind =
        e8VocabTokenizer
    ; artifactLabel =
        "E8 vocab/tokenizer"
    ; disposition =
        diagnosticOnly
    ; targetLanes =
        LILA-R1 ∷ []
    ; priority =
        noPortPriority
    ; triage =
        "diagnostic-only LILA-R1"
    ; acceptanceBoundary =
        "Tokenizer/vocabulary diagnostic only; not an E8 root enumeration"
    ; promotionBoundary =
        "No LILA-R1 E8 carrier receipt is promoted"
    }

lilaTrainingDynamicsEntry :
  SiblingPortMatrixEntry
lilaTrainingDynamicsEntry =
  record
    { artifactKind =
        lilaTrainingDynamics
    ; artifactLabel =
        "LILA training dynamics"
    ; disposition =
        diagnosticOnly
    ; targetLanes =
        LILA-R1 ∷ []
    ; priority =
        noPortPriority
    ; triage =
        "diagnostic-only LILA-R1"
    ; acceptanceBoundary =
        "Training dynamics diagnostics only; not a constructive lattice or carrier receipt"
    ; promotionBoundary =
        "No LILA-R1 closure or carrier gate is promoted"
    }

quantumCurvatureExperimentsEntry :
  SiblingPortMatrixEntry
quantumCurvatureExperimentsEntry =
  record
    { artifactKind =
        quantumCurvatureExperiments
    ; artifactLabel =
        "quantum/curvature experiments"
    ; disposition =
        diagnosticOnly
    ; targetLanes =
        W5 ∷ W6 ∷ []
    ; priority =
        noPortPriority
    ; triage =
        "diagnostic-only W5/W6"
    ; acceptanceBoundary =
        "Experimental diagnostics only; no physics consumer source receipt is accepted"
    ; promotionBoundary =
        "No W5 or W6 physics closure gate is promoted"
    }

tradingVulkanCodecEntry :
  SiblingPortMatrixEntry
tradingVulkanCodecEntry =
  record
    { artifactKind =
        tradingVulkanCodec
    ; artifactLabel =
        "trading/Vulkan/codec"
    ; disposition =
        ignoreForClosure
    ; targetLanes =
        []
    ; priority =
        ignoredPriority
    ; triage =
        "ignore-for-closure"
    ; acceptanceBoundary =
        "Out of scope for closure porting"
    ; promotionBoundary =
        "Ignored rows construct no closure authority"
    }

canonicalSiblingPortMatrixEntries :
  List SiblingPortMatrixEntry
canonicalSiblingPortMatrixEntries =
  dashifineContractionCertificateEntry
  ∷ dashifineLyapunovEnergyEntry
  ∷ fejerClosestPointEntry
  ∷ signatureSurfaceEntry
  ∷ coneOrbitProfileEntry
  ∷ hepDataLensProjectionEntry
  ∷ seamCertificateEntry
  ∷ base369LogicTlureyOverflowEntry
  ∷ gpuIrPrimitivesEntry
  ∷ leanMoonshineArithmeticEntry
  ∷ e8VocabTokenizerEntry
  ∷ lilaTrainingDynamicsEntry
  ∷ quantumCurvatureExperimentsEntry
  ∷ tradingVulkanCodecEntry
  ∷ []

data SiblingPortMatrixPromotedReceipt : Set where

siblingPortMatrixPromotionImpossibleHere :
  SiblingPortMatrixPromotedReceipt →
  ⊥
siblingPortMatrixPromotionImpossibleHere ()

record SiblingMathPortingMatrix : Setω where
  field
    status :
      SiblingMathPortingMatrixStatus

    promotesAnyGate :
      Bool

    promotesAnyGateIsFalse :
      promotesAnyGate ≡ false

    acceptsExternalAuthority :
      Bool

    acceptsExternalAuthorityIsFalse :
      acceptsExternalAuthority ≡ false

    rebindsClosureObligation :
      Bool

    rebindsClosureObligationIsFalse :
      rebindsClosureObligation ≡ false

    artifactKinds :
      List SiblingArtifactKind

    artifactKindsAreCanonical :
      artifactKinds ≡ canonicalSiblingArtifactKinds

    matrixEntries :
      List SiblingPortMatrixEntry

    matrixEntriesAreCanonical :
      matrixEntries ≡ canonicalSiblingPortMatrixEntries

    priorityStack :
      List String

    priorityStackIsCanonical :
      priorityStack ≡ canonicalPriorityStack

    diagramCoordinationNotes :
      List String

    nonPromotionBoundary :
      List String

    promotedReceiptBlocked :
      SiblingPortMatrixPromotedReceipt →
      ⊥

canonicalSiblingMathPortingMatrix :
  SiblingMathPortingMatrix
canonicalSiblingMathPortingMatrix =
  record
    { status =
        siblingPortMatrixRecordedNoPromotion
    ; promotesAnyGate =
        false
    ; promotesAnyGateIsFalse =
        refl
    ; acceptsExternalAuthority =
        false
    ; acceptsExternalAuthorityIsFalse =
        refl
    ; rebindsClosureObligation =
        false
    ; rebindsClosureObligationIsFalse =
        refl
    ; artifactKinds =
        canonicalSiblingArtifactKinds
    ; artifactKindsAreCanonical =
        refl
    ; matrixEntries =
        canonicalSiblingPortMatrixEntries
    ; matrixEntriesAreCanonical =
        refl
    ; priorityStack =
        canonicalPriorityStack
    ; priorityStackIsCanonical =
        refl
    ; diagramCoordinationNotes =
        "Diagrams should add a SIB-MATRIX coordination node pointing to this module"
        ∷ "This worker lane does not edit diagrams, shared docs, or P0 indexes"
        ∷ []
    ; nonPromotionBoundary =
        "This matrix classifies sibling artifacts only"
        ∷ "Port-to-Agda rows require DASHI-native reproof before any gate use"
        ∷ "HEPData lens/projection remains projection-candidate only until DASHI-native sigma exists"
        ∷ "Citation-only rows do not become receipts"
        ∷ "Diagnostic-only rows do not become receipts"
        ∷ "Ignored rows are outside closure scope"
        ∷ "No gate promotion, external authority acceptance, or closure-obligation rebind is constructed here"
        ∷ []
    ; promotedReceiptBlocked =
        siblingPortMatrixPromotionImpossibleHere
    }

canonicalSiblingMathPortingMatrixStatus :
  SiblingMathPortingMatrixStatus
canonicalSiblingMathPortingMatrixStatus =
  siblingPortMatrixRecordedNoPromotion
