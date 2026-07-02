module DASHI.Biology.ProteinRepresentationCarrier where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import Data.Empty using (⊥)

import DASHI.Core.ContextIndexedEncoding as CIE
import DASHI.Promotion.ProteinEncoding as PE

------------------------------------------------------------------------
-- Protein representation carrier
--
-- The missing bridge:
--
--   ProteinSymbol (inhabited)     ← genetic-code level
--        ↓
--   ProteinRepresentationCarrier  ← sequence + external payloads
--        ↓
--   Property projection           ← task-specific charts
--        ↓
--   Assay residual                ← experimental authority
--        ↓
--   Calibration receipt           ← no promotion without closure
--
-- This is NOT:
--   • biological causation
--   • folding authority
--   • therapeutic authority
--   • clinical authority
--
-- It is a typed bridge between finite genetic-code symbols,
-- external structural/embedding payloads, and task-specific
-- property projections, all guarded by the DASHI fail-closed
-- philosophy.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. The carrier record (parameterized over external payload types)
------------------------------------------------------------------------

-- ProteinRepresentationCarrier packages the multiple surfaces that
-- together describe a protein candidate in a form ready for
-- structure-aware property prediction.
--
-- The sequence is concretely inhabited (by translation of a genetic
-- code).  The structural, embedding, and assay-context surfaces are
-- parameterized so external callers can instantiate them with real
-- payload types.  The DASHI canonical instance sets all three to ⊤,
-- keeping them abstract and non-promoted.

record ProteinRepresentationCarrier (StructureSurface EmbeddingSurface AssayContextSurface : Set) : Set where
  field
    -- Amino-acid sequence (from genetic-code translation)
    sequenceSurface : PE.ProteinSequence

    -- Structural surface: fold class, 3Di tokens, or coordinates.
    -- Carried externally; DASHI does not resolve structure prediction.
    structureSurface : StructureSurface

    -- PLM embedding: a vector in the embedding space of a frozen
    -- protein language model (e.g. ProstT5, ESM).
    -- Carried externally; DASHI does not host the embedding model.
    embeddingSurface : EmbeddingSurface

    -- Experimental context under which any assay data were collected.
    -- Carried externally; DASHI does not resolve experimental protocol.
    assayContextSurface : AssayContextSurface

    -- The set of developability properties that this carrier has been
    -- projected onto (typically all six: solubility, thermostability,
    -- aggregation, yield, folding stability, production).
    propertySurfaces : List PE.Property

open ProteinRepresentationCarrier public

-- Canonical carrier with all external payloads collapsed to ⊤.
-- This is the DASHI-safe default: the carrier admits any protein
-- sequence while the external surfaces remain abstract.

canonicalProteinRepresentationCarrier : PE.ProteinSequence → ProteinRepresentationCarrier ⊤ ⊤ ⊤
canonicalProteinRepresentationCarrier seq = record
  { sequenceSurface     = seq
  ; structureSurface    = tt
  ; embeddingSurface    = tt
  ; assayContextSurface = tt
  ; propertySurfaces    = PE.allProperties
  }

------------------------------------------------------------------------
-- 2. Relationship to the finite genetic code
------------------------------------------------------------------------

-- The sequence is concretely inhabited because it is obtained by
-- translating a DNA/RNA sequence under some translation context.
-- The genetic-code level (Codon → ProteinSymbol) is real and finite.
-- This carrier layer is built on top of that finite base.

sequenceInhabited : (seq : PE.ProteinSequence) → Bool
sequenceInhabited []       = true
sequenceInhabited (_ ∷ _)  = true

sequenceInhabitedIsTrue : (seq : PE.ProteinSequence) → sequenceInhabited seq ≡ true
sequenceInhabitedIsTrue []       = refl
sequenceInhabitedIsTrue (_ ∷ _)  = refl

------------------------------------------------------------------------
-- 3. Guards
------------------------------------------------------------------------

-- Forbidden claims that the carrier does NOT license
data ProteinRepresentationForbiddenClaim : Set where
  FoldingAuthorityClaim        : ProteinRepresentationForbiddenClaim
  DiseaseCausationClaim        : ProteinRepresentationForbiddenClaim
  TherapeuticAuthorityClaim    : ProteinRepresentationForbiddenClaim
  ClinicalAuthorityClaim       : ProteinRepresentationForbiddenClaim
  CellFateClosureClaim         : ProteinRepresentationForbiddenClaim

canonicalForbiddenClaims : List ProteinRepresentationForbiddenClaim
canonicalForbiddenClaims =
  FoldingAuthorityClaim
  ∷ DiseaseCausationClaim
  ∷ TherapeuticAuthorityClaim
  ∷ ClinicalAuthorityClaim
  ∷ CellFateClosureClaim
  ∷ []

-- Allowed operations on the carrier
data ProteinRepresentationAllowedOperation : Set where
  SequenceProjection      : ProteinRepresentationAllowedOperation
  StructureAwareEncoding  : ProteinRepresentationAllowedOperation
  EmbeddingExtraction     : ProteinRepresentationAllowedOperation
  PropertyProjection      : ProteinRepresentationAllowedOperation
  ResidualMeasurement     : ProteinRepresentationAllowedOperation
  PostHocCalibration      : ProteinRepresentationAllowedOperation
  AssayComparison         : ProteinRepresentationAllowedOperation

canonicalAllowedOperations : List ProteinRepresentationAllowedOperation
canonicalAllowedOperations =
  SequenceProjection
  ∷ StructureAwareEncoding
  ∷ EmbeddingExtraction
  ∷ PropertyProjection
  ∷ ResidualMeasurement
  ∷ PostHocCalibration
  ∷ AssayComparison
  ∷ []

-- Guards that the carrier enforces
data ProteinRepresentationGuard : Set where
  NoFoldingAuthorityClaim        : ProteinRepresentationGuard
  NoDiseaseCausationClaim        : ProteinRepresentationGuard
  NoTherapeuticAuthorityClaim    : ProteinRepresentationGuard
  NoClinicalAuthorityClaim       : ProteinRepresentationGuard
  NoCellFateClosureClaim         : ProteinRepresentationGuard
  NoExternalAuthorityBypass      : ProteinRepresentationGuard

canonicalGuards : List ProteinRepresentationGuard
canonicalGuards =
  NoFoldingAuthorityClaim
  ∷ NoDiseaseCausationClaim
  ∷ NoTherapeuticAuthorityClaim
  ∷ NoClinicalAuthorityClaim
  ∷ NoCellFateClosureClaim
  ∷ NoExternalAuthorityBypass
  ∷ []

------------------------------------------------------------------------
-- 4. The carrier as a ContextIndexedEncoding instance
------------------------------------------------------------------------

-- The carrier becomes a context-indexed encoding where:
--   Carrier   = ProteinRepresentationCarrier
--   Context   = PE.Property  (which chart to project)
--   Observable = PE.PropertySurface p (packaged as Σ)
--
-- This formalises "protein = typed latent carrier with multiple
-- projections": the carrier has many surfaces, and each property
-- is a projection π(carrier, property) onto that chart.

ObservablePackage : Set
ObservablePackage = Σ PE.Property λ p → PE.PropertySurface p

projection : ProteinRepresentationCarrier ⊤ ⊤ ⊤ → PE.Property → ObservablePackage
projection _ p = (p , tt)

transportObs : PE.Property → PE.Property → ObservablePackage → ObservablePackage
transportObs _ _ (p , o) = (p , o)

CarrierEncoding : CIE.ContextIndexedEncoding
  (ProteinRepresentationCarrier ⊤ ⊤ ⊤) PE.Property ObservablePackage
CarrierEncoding = record
  { π                      = projection
  ; transport              = transportObs
  ; residual               = λ p p' (c : ProteinRepresentationCarrier ⊤ ⊤ ⊤) → ⊤
  ; contextDependent       = true
  ; contextDependentIsTrue = refl
  ; promotionGateCarrier   = ⊤
  ; promotionGateClosed    = λ _ → false
  ; encodingGuards         =
      "noFoldingAuthority"
      ∷ "noTherapeuticAuthority"
      ∷ "noClinicalAuthority"
      ∷ []
  ; forbiddenPromotions    =
      "carrierPromotedToCausation"
      ∷ "structurePromotedToGroundTruth"
      ∷ "embeddingPromotedToCompleteRepresentation"
      ∷ []
  ; allowedOperations      =
      "sequenceProjection"
      ∷ "structureAwareEncoding"
      ∷ "propertyProjection"
      ∷ "residualMeasurement"
      ∷ "postHocCalibration"
      ∷ []
  ; encodingReading        =
      "Protein representation carrier as context-indexed encoding: carrier surfaces are separate from property projections. The carrier bundles sequence, structural, embedding, and assay-context surfaces explicitly, without promoting any single surface to biological causation."
  }

------------------------------------------------------------------------
-- 5. Non-promotion certificate
------------------------------------------------------------------------

record ProteinRepresentationNonPromotionCertificate : Set where
  field
    foldingNotAuthorized     : Bool
    foldingNotAuthorizedIsTrue : foldingNotAuthorized ≡ true
    diseaseNotAuthorized     : Bool
    diseaseNotAuthorizedIsTrue : diseaseNotAuthorized ≡ true
    therapeuticNotAuthorized : Bool
    therapeuticNotAuthorizedIsTrue : therapeuticNotAuthorized ≡ true
    clinicalNotAuthorized    : Bool
    clinicalNotAuthorizedIsTrue : clinicalNotAuthorized ≡ true
    cellFateNotAuthorized    : Bool
    cellFateNotAuthorizedIsTrue : cellFateNotAuthorized ≡ true
    guardsMatch              : List ProteinRepresentationGuard
    forbiddenMatch           : List ProteinRepresentationForbiddenClaim
    allowedMatch             : List ProteinRepresentationAllowedOperation
    certificateReading       : String

open ProteinRepresentationNonPromotionCertificate public

canonicalProteinRepresentationNonPromotionCertificate :
  ProteinRepresentationNonPromotionCertificate
canonicalProteinRepresentationNonPromotionCertificate = record
  { foldingNotAuthorized          = true
  ; foldingNotAuthorizedIsTrue    = refl
  ; diseaseNotAuthorized          = true
  ; diseaseNotAuthorizedIsTrue    = refl
  ; therapeuticNotAuthorized      = true
  ; therapeuticNotAuthorizedIsTrue = refl
  ; clinicalNotAuthorized         = true
  ; clinicalNotAuthorizedIsTrue   = refl
  ; cellFateNotAuthorized         = true
  ; cellFateNotAuthorizedIsTrue   = refl
  ; guardsMatch                   = canonicalGuards
  ; forbiddenMatch                = canonicalForbiddenClaims
  ; allowedMatch                  = canonicalAllowedOperations
  ; certificateReading            =
      "The canonical protein representation carrier is non-promoting: it bundles sequence, structure, embedding, and assay-context surfaces without granting folding, disease, therapeutic, clinical, or cell-fate authority. All external payloads are abstract (⊤) and no single surface is promoted to biological causation."
  }

------------------------------------------------------------------------
-- 6. The DASHI placement slogan
------------------------------------------------------------------------

--   ProteinSymbol is inhabited.           ← genetic-code level (real, finite)
--   ProteinCandidate is guarded.          ← promotion level (fail-closed)
--   ProteinRepresentationCarrier is the   ← this module
--     missing bridge.
--
-- The carrier lives between the two:
-- it is concretely typed (has a sequence)
-- while keeping external payloads abstract
-- and property projections guarded.
