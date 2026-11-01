module DASHI.Ontology.WikidataInterpretiveDiagnosticExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.WikidataDerivationFibreBridge as Fibre
import DASHI.Ontology.CrossOntologyContradictionAttributionExact as Attribution

------------------------------------------------------------------------
-- Interpretive diagnostic surface.
--
-- Cross-domain calibration:
-- Alice Brown et al. / Finn & Brown corpus work motivates retaining source,
-- coding frame, interpreter location, uncertainty, missingness and a
-- contestability route.  The theorem layer below is DASHI-local and does not
-- attribute ontology-validation conclusions to those education papers.
--
-- Alice Brown; Megan Kimber (2026),
-- "Repositioning Student Voice and Agency: A Call for the Epistemic Expansion
-- of Scholarship of Teaching and Learning Inquiry",
-- Active Learning in Higher Education 27(2), 253-264.
-- DOI: 10.1177/14697874261426374.
--
-- Roxanne Finn; Alice Brown (2025),
-- "Custodians of an ecology of data: Foundational theory and practice for data
-- analysis in a complex world", Qualitative Research 25(1), 110-129.
-- DOI: 10.1177/14687941241234293.
------------------------------------------------------------------------

data DiagnosticInterpreter : Set where
  jmdLeanChecker : DiagnosticInterpreter
  sensibLawScanner : DiagnosticInterpreter
  zelphTraversal : DiagnosticInterpreter
  wdqsExploration : DiagnosticInterpreter
  humanReview : DiagnosticInterpreter

record DiagnosticInterpretation (claim : Fibre.ClaimBase) : Set where
  constructor diagnosticInterpretation
  field
    attributionFibre : Attribution.AttributedDerivationFibre claim
    sourceSurface : String
    sourceSnapshot : String
    ruleOrCodingFrame : String
    interpreter : DiagnosticInterpreter
    producedDiagnostic : String
    uncertaintyReceipt : String
    missingnessReceipt : String
    contestabilityRoute : String
    outputCandidateOnly : Bool
    outputCandidateOnlyIsTrue : outputCandidateOnly ≡ true
    outputNotSemanticIdentity : Bool
    outputNotSemanticIdentityIsTrue : outputNotSemanticIdentity ≡ true

open DiagnosticInterpretation public

data DiagnosticOutputImpliesOntologyTruthPermission : Set where

diagnosticOutputCannotSelfPromoteToOntologyTruth :
  DiagnosticOutputImpliesOntologyTruthPermission → ⊥
diagnosticOutputCannotSelfPromoteToOntologyTruth ()

data MissingnessCanBeDiscardedPermission : Set where

missingnessCannotBeDiscardedBeforePromotion :
  MissingnessCanBeDiscardedPermission → ⊥
missingnessCannotBeDiscardedBeforePromotion ()

canonicalAlignmentStressDiagnostic :
  DiagnosticInterpretation Attribution.alignmentStressClaim
canonicalAlignmentStressDiagnostic =
  diagnosticInterpretation
    Attribution.alignmentLocalStressFibre
    "source ontology + concrete target graph"
    "fixture:alignment-local-stress:v1"
    "declared cross-ontology alignment obligations"
    jmdLeanChecker
    "alignment-local conflict candidate"
    "support and counter-support are retained separately"
    "none in this fixture; real acquisition must record omissions explicitly"
    "working-group review may contest source, mapping, inference language or target interpretation"
    true refl
    true refl

record InterpretiveDiagnosticBoundary : Set where
  constructor interpretiveDiagnosticBoundary
  field
    checkerOutputIsCandidate : Bool
    checkerOutputIsOntologyTruth : Bool
    frameMustRemainExplicit : Bool
    missingnessMustRemainExplicit : Bool
    contestabilityMustRemainExplicit : Bool

canonicalInterpretiveDiagnosticBoundary : InterpretiveDiagnosticBoundary
canonicalInterpretiveDiagnosticBoundary =
  interpretiveDiagnosticBoundary true false true true true
