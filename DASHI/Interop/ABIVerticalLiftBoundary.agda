module DASHI.Interop.ABIVerticalLiftBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- ABI vertical lift and bounded-overhead bridge boundary.
--
-- This module records ABI transforms as bridge targets only.  It provides
-- rows for canonical artifact-to-semantics lift examples and records a
-- bounded-overhead accounting surface.  It does not claim an exact
-- Kolmogorov-semantic theorem, does not accept semantic-AIT authority from
-- context strings, and does not promote the bridge to a physical theorem.

data ABITransformKind : Set where
  elfToCar :
    ABITransformKind

  dagCborToIpld :
    ABITransformKind

  machineCodeToFractran :
    ABITransformKind

  agdaToLean :
    ABITransformKind

  contextOnlyTransform :
    String →
    ABITransformKind

canonicalABITransformKinds :
  List ABITransformKind
canonicalABITransformKinds =
  elfToCar
  ∷ dagCborToIpld
  ∷ machineCodeToFractran
  ∷ agdaToLean
  ∷ []

record ABITransformRow : Set where
  field
    transformKind :
      ABITransformKind

    sourceArtifact :
      String

    targetArtifact :
      String

    sourceSemanticSurface :
      String

    targetSemanticSurface :
      String

    transformReading :
      String

    verticalPreservesSemantics :
      Bool

    verticalPreservesSemanticsIsTrue :
      verticalPreservesSemantics ≡ true

    boundedOverheadRecorded :
      Bool

    boundedOverheadRecordedIsTrue :
      boundedOverheadRecorded ≡ true

    exactEquivalencePromoted :
      Bool

    exactEquivalencePromotedIsFalse :
      exactEquivalencePromoted ≡ false

open ABITransformRow public

canonicalELFCARVerticalLiftRow :
  ABITransformRow
canonicalELFCARVerticalLiftRow =
  record
    { transformKind =
        elfToCar
    ; sourceArtifact =
        "ELF executable or object file"
    ; targetArtifact =
        "CAR archive row containing the ELF payload and manifest"
    ; sourceSemanticSurface =
        "ABI-observable entry points, sections, symbols, relocations, and calling convention metadata"
    ; targetSemanticSurface =
        "content-addressed artifact row with the same ABI-observable fields named as payload semantics"
    ; transformReading =
        "Canonical vertical lift target: ELF/CAR packaging preserves the selected ABI semantic row while overhead is recorded as manifest plus block framing."
    ; verticalPreservesSemantics =
        true
    ; verticalPreservesSemanticsIsTrue =
        refl
    ; boundedOverheadRecorded =
        true
    ; boundedOverheadRecordedIsTrue =
        refl
    ; exactEquivalencePromoted =
        false
    ; exactEquivalencePromotedIsFalse =
        refl
    }

canonicalDAGCBORIPLDVerticalLiftRow :
  ABITransformRow
canonicalDAGCBORIPLDVerticalLiftRow =
  record
    { transformKind =
        dagCborToIpld
    ; sourceArtifact =
        "DAG-CBOR block"
    ; targetArtifact =
        "IPLD typed node"
    ; sourceSemanticSurface =
        "canonical CBOR map/list/scalar structure under DAG-CBOR constraints"
    ; targetSemanticSurface =
        "IPLD data model node with link and scalar interpretation"
    ; transformReading =
        "DAG-CBOR/IPLD is recorded as a canonical data-model lift with bounded codec overhead, not as a theorem about all encodings."
    ; verticalPreservesSemantics =
        true
    ; verticalPreservesSemanticsIsTrue =
        refl
    ; boundedOverheadRecorded =
        true
    ; boundedOverheadRecordedIsTrue =
        refl
    ; exactEquivalencePromoted =
        false
    ; exactEquivalencePromotedIsFalse =
        refl
    }

canonicalMachineCodeFRACTRANVerticalLiftRow :
  ABITransformRow
canonicalMachineCodeFRACTRANVerticalLiftRow =
  record
    { transformKind =
        machineCodeToFractran
    ; sourceArtifact =
        "machine-code trace window"
    ; targetArtifact =
        "FRACTRAN trace receipt"
    ; sourceSemanticSurface =
        "finite instruction trace with register and memory observations named by the ABI row"
    ; targetSemanticSurface =
        "finite rational-program trace carrying the same selected observations"
    ; transformReading =
        "MachineCode/FRACTRAN is a bounded finite-trace bridge target; it is not a total compiler-correctness theorem."
    ; verticalPreservesSemantics =
        true
    ; verticalPreservesSemanticsIsTrue =
        refl
    ; boundedOverheadRecorded =
        true
    ; boundedOverheadRecordedIsTrue =
        refl
    ; exactEquivalencePromoted =
        false
    ; exactEquivalencePromotedIsFalse =
        refl
    }

canonicalAgdaLeanVerticalLiftRow :
  ABITransformRow
canonicalAgdaLeanVerticalLiftRow =
  record
    { transformKind =
        agdaToLean
    ; sourceArtifact =
        "Agda module interface row"
    ; targetArtifact =
        "Lean declaration row"
    ; sourceSemanticSurface =
        "named declarations, constructors, record fields, and explicit theorem-status booleans"
    ; targetSemanticSurface =
        "corresponding declaration table and theorem-status booleans after translation"
    ; transformReading =
        "Agda/Lean is a proof-assistant interface bridge target; only named rows and booleans are preserved here."
    ; verticalPreservesSemantics =
        true
    ; verticalPreservesSemanticsIsTrue =
        refl
    ; boundedOverheadRecorded =
        true
    ; boundedOverheadRecordedIsTrue =
        refl
    ; exactEquivalencePromoted =
        false
    ; exactEquivalencePromotedIsFalse =
        refl
    }

canonicalABIVerticalLiftRows :
  List ABITransformRow
canonicalABIVerticalLiftRows =
  canonicalELFCARVerticalLiftRow
  ∷ canonicalDAGCBORIPLDVerticalLiftRow
  ∷ canonicalMachineCodeFRACTRANVerticalLiftRow
  ∷ canonicalAgdaLeanVerticalLiftRow
  ∷ []

record SourceContextRow : Set where
  field
    sourceLabel :
      String

    sourceReading :
      String

    contextOnly :
      Bool

    contextOnlyIsTrue :
      contextOnly ≡ true

    externalAuthorityAccepted :
      Bool

    externalAuthorityAcceptedIsFalse :
      externalAuthorityAccepted ≡ false

open SourceContextRow public

kolmogorovInvarianceContextRow :
  SourceContextRow
kolmogorovInvarianceContextRow =
  record
    { sourceLabel =
        "Kolmogorov invariance theorem"
    ; sourceReading =
        "context-only: invariance up to an additive constant motivates bounded-overhead accounting between description languages; this module does not prove an exact semantic theorem from it."
    ; contextOnly =
        true
    ; contextOnlyIsTrue =
        refl
    ; externalAuthorityAccepted =
        false
    ; externalAuthorityAcceptedIsFalse =
        refl
    }

wu2026SemanticAITContextRow :
  SourceContextRow
wu2026SemanticAITContextRow =
  record
    { sourceLabel =
        "Wu 2026 semantic AIT"
    ; sourceReading =
        "context-only: cited as a semantic-AIT motivation string for future authority intake; no external authority is accepted by this Agda boundary."
    ; contextOnly =
        true
    ; contextOnlyIsTrue =
        refl
    ; externalAuthorityAccepted =
        false
    ; externalAuthorityAcceptedIsFalse =
        refl
    }

canonicalABIContextRows :
  List SourceContextRow
canonicalABIContextRows =
  kolmogorovInvarianceContextRow
  ∷ wu2026SemanticAITContextRow
  ∷ []

record ABIBoundedOverheadRow : Set where
  field
    overheadName :
      String

    overheadBoundReading :
      String

    boundForm :
      String

    boundedOverheadRecorded :
      Bool

    boundedOverheadRecordedIsTrue :
      boundedOverheadRecorded ≡ true

open ABIBoundedOverheadRow public

canonicalABIBoundedOverheadRow :
  ABIBoundedOverheadRow
canonicalABIBoundedOverheadRow =
  record
    { overheadName =
        "ABI vertical lift bounded overhead"
    ; overheadBoundReading =
        "Each row records overhead as finite manifest, codec, trace, or declaration-table framing relative to the selected source artifact row."
    ; boundForm =
        "overhead <= row-header + finite metadata + selected-trace/declaration framing"
    ; boundedOverheadRecorded =
        true
    ; boundedOverheadRecordedIsTrue =
        refl
    }

data ABIBridgeNonClaim : Set where
  noExactKolmogorovSemanticTheorem :
    ABIBridgeNonClaim

  noSemanticAITAuthorityAcceptance :
    ABIBridgeNonClaim

  noPhysicalPromotion :
    ABIBridgeNonClaim

  noGlobalCompilerCorrectness :
    ABIBridgeNonClaim

  noAllEncodingEquivalence :
    ABIBridgeNonClaim

canonicalABIBridgeNonClaims :
  List ABIBridgeNonClaim
canonicalABIBridgeNonClaims =
  noExactKolmogorovSemanticTheorem
  ∷ noSemanticAITAuthorityAcceptance
  ∷ noPhysicalPromotion
  ∷ noGlobalCompilerCorrectness
  ∷ noAllEncodingEquivalence
  ∷ []

record ABIVerticalLiftBoundary : Set where
  field
    artifactRows :
      List String

    semanticRows :
      List String

    transformKinds :
      List ABITransformKind

    transformKindsAreCanonical :
      transformKinds ≡ canonicalABITransformKinds

    verticalLiftRows :
      List ABITransformRow

    verticalLiftRowsAreCanonical :
      verticalLiftRows ≡ canonicalABIVerticalLiftRows

    boundedOverheadRow :
      ABIBoundedOverheadRow

    boundedOverheadRowIsCanonical :
      boundedOverheadRow ≡ canonicalABIBoundedOverheadRow

    sourceContextRows :
      List SourceContextRow

    sourceContextRowsAreCanonical :
      sourceContextRows ≡ canonicalABIContextRows

    nonClaims :
      List ABIBridgeNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalABIBridgeNonClaims

    verticalPreservesSemantics :
      Bool

    verticalPreservesSemanticsIsTrue :
      verticalPreservesSemantics ≡ true

    boundedOverheadRecorded :
      Bool

    boundedOverheadRecordedIsTrue :
      boundedOverheadRecorded ≡ true

    exactKolmogorovSemanticTheorem :
      Bool

    exactKolmogorovSemanticTheoremIsFalse :
      exactKolmogorovSemanticTheorem ≡ false

    semanticAITExternalAuthorityAccepted :
      Bool

    semanticAITExternalAuthorityAcceptedIsFalse :
      semanticAITExternalAuthorityAccepted ≡ false

    physicalPromotion :
      Bool

    physicalPromotionIsFalse :
      physicalPromotion ≡ false

open ABIVerticalLiftBoundary public

canonicalArtifactRows :
  List String
canonicalArtifactRows =
  "ELF executable or object file"
  ∷ "CAR archive row"
  ∷ "DAG-CBOR block"
  ∷ "IPLD typed node"
  ∷ "machine-code trace window"
  ∷ "FRACTRAN trace receipt"
  ∷ "Agda module interface row"
  ∷ "Lean declaration row"
  ∷ []

canonicalSemanticRows :
  List String
canonicalSemanticRows =
  "ABI-observable symbols, sections, relocations, entry points, and calling conventions"
  ∷ "content-addressed payload semantics"
  ∷ "DAG-CBOR canonical data-model semantics"
  ∷ "IPLD link and scalar node semantics"
  ∷ "finite machine observation trace semantics"
  ∷ "FRACTRAN replay observation semantics"
  ∷ "proof-assistant declaration and theorem-status semantics"
  ∷ []

canonicalABIVerticalLiftBoundary :
  ABIVerticalLiftBoundary
canonicalABIVerticalLiftBoundary =
  record
    { artifactRows =
        canonicalArtifactRows
    ; semanticRows =
        canonicalSemanticRows
    ; transformKinds =
        canonicalABITransformKinds
    ; transformKindsAreCanonical =
        refl
    ; verticalLiftRows =
        canonicalABIVerticalLiftRows
    ; verticalLiftRowsAreCanonical =
        refl
    ; boundedOverheadRow =
        canonicalABIBoundedOverheadRow
    ; boundedOverheadRowIsCanonical =
        refl
    ; sourceContextRows =
        canonicalABIContextRows
    ; sourceContextRowsAreCanonical =
        refl
    ; nonClaims =
        canonicalABIBridgeNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; verticalPreservesSemantics =
        true
    ; verticalPreservesSemanticsIsTrue =
        refl
    ; boundedOverheadRecorded =
        true
    ; boundedOverheadRecordedIsTrue =
        refl
    ; exactKolmogorovSemanticTheorem =
        false
    ; exactKolmogorovSemanticTheoremIsFalse =
        refl
    ; semanticAITExternalAuthorityAccepted =
        false
    ; semanticAITExternalAuthorityAcceptedIsFalse =
        refl
    ; physicalPromotion =
        false
    ; physicalPromotionIsFalse =
        refl
    }

canonicalABIVerticalLiftBoundaryPreservesSemantics :
  verticalPreservesSemantics canonicalABIVerticalLiftBoundary ≡ true
canonicalABIVerticalLiftBoundaryPreservesSemantics =
  verticalPreservesSemanticsIsTrue canonicalABIVerticalLiftBoundary

canonicalABIVerticalLiftBoundaryRecordsBoundedOverhead :
  boundedOverheadRecorded canonicalABIVerticalLiftBoundary ≡ true
canonicalABIVerticalLiftBoundaryRecordsBoundedOverhead =
  boundedOverheadRecordedIsTrue canonicalABIVerticalLiftBoundary

canonicalABIVerticalLiftBoundaryHasNoExactKolmogorovSemanticTheorem :
  exactKolmogorovSemanticTheorem canonicalABIVerticalLiftBoundary ≡ false
canonicalABIVerticalLiftBoundaryHasNoExactKolmogorovSemanticTheorem =
  exactKolmogorovSemanticTheoremIsFalse canonicalABIVerticalLiftBoundary

canonicalABIVerticalLiftBoundaryRejectsSemanticAITAuthority :
  semanticAITExternalAuthorityAccepted canonicalABIVerticalLiftBoundary ≡ false
canonicalABIVerticalLiftBoundaryRejectsSemanticAITAuthority =
  semanticAITExternalAuthorityAcceptedIsFalse canonicalABIVerticalLiftBoundary

canonicalABIVerticalLiftBoundaryHasNoPhysicalPromotion :
  physicalPromotion canonicalABIVerticalLiftBoundary ≡ false
canonicalABIVerticalLiftBoundaryHasNoPhysicalPromotion =
  physicalPromotionIsFalse canonicalABIVerticalLiftBoundary
