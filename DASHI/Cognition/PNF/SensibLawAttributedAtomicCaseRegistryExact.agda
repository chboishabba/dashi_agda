module DASHI.Cognition.PNF.SensibLawAttributedAtomicCaseRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawAtomicCaseOutcomeCoherenceExact as Coherence
import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Provenance

------------------------------------------------------------------------
-- ATTRIBUTED ATOMIC CASE REGISTRY
--
-- An atomic legal test has three independent attribution fibres:
--   1. provenance of the repository proposition defining the legal atom;
--   2. provenance of the concrete case outcome evidence proposition;
--   3. provenance of the repository evaluation that maps those materials to a
--      balanced-ternary fit/failure/unresolved gate.
--
-- The first two may be DASHI reconstructions even when their source receipts
-- point to primary judicial/statutory material. The third is not silently
-- attributed back to the source merely because the source supports the inputs.
------------------------------------------------------------------------

data AtomicEntryOutcomeLineage
    (registry : Coherence.AtomicCaseRegistry)
    {p}
    (entry : Coherence.Entry registry p) : Set₁ where

  unresolvedOutcomeLineage :
    Atomic.gate (Coherence.canonicalTestFor registry entry) ≡ BT.zero →
    String →
    AtomicEntryOutcomeLineage registry entry

  positiveOutcomeLineage :
    (positive : Atomic.gate (Coherence.canonicalTestFor registry entry) ≡ BT.pos) →
    Provenance.ClaimLineageReceipt
      (Atomic.evidenceProposition
        (Atomic.positiveOutcomeEvidence
          (Coherence.canonicalTestFor registry entry)
          (Atomic.positiveWitness
            (Coherence.canonicalTestFor registry entry)
            positive))) →
    AtomicEntryOutcomeLineage registry entry

  negativeOutcomeLineage :
    (negative : Atomic.gate (Coherence.canonicalTestFor registry entry) ≡ BT.neg) →
    Provenance.ClaimLineageReceipt
      (Atomic.evidenceProposition
        (Atomic.negativeOutcomeEvidence
          (Coherence.canonicalTestFor registry entry)
          (Atomic.negativeFailureWitness
            (Coherence.canonicalTestFor registry entry)
            negative))) →
    AtomicEntryOutcomeLineage registry entry

data AtomicEvaluationLineage
    (registry : Coherence.AtomicCaseRegistry)
    {p}
    (entry : Coherence.Entry registry p) :
    Provenance.LegalClaimProvenanceStage → Set where

  repositoryEvaluationInference :
    String →
    AtomicEvaluationLineage registry entry Provenance.crossSourceInference

  repositoryEvaluationTheorem :
    String →
    String →
    AtomicEvaluationLineage registry entry Provenance.repositoryTheoremExtension

  externallyAdjudicatedEvaluation :
    String →
    String →
    AtomicEvaluationLineage registry entry Provenance.promotionOrExternalAdjudication

AtomicEvaluationLineageReceipt :
  (registry : Coherence.AtomicCaseRegistry) →
  ∀ {p} →
  Coherence.Entry registry p → Set
AtomicEvaluationLineageReceipt registry entry =
  Σ Provenance.LegalClaimProvenanceStage λ stage →
    AtomicEvaluationLineage registry entry stage

record AttributedAtomicCaseRegistry
    (registry : Coherence.AtomicCaseRegistry) : Set₁ where
  constructor attributed-atomic-case-registry
  field
    definitionLineageFor :
      ∀ {p} →
      (entry : Coherence.Entry registry p) →
      Provenance.ClaimLineageReceipt p

    outcomeLineageFor :
      ∀ {p} →
      (entry : Coherence.Entry registry p) →
      AtomicEntryOutcomeLineage registry entry

    evaluationLineageFor :
      ∀ {p} →
      (entry : Coherence.Entry registry p) →
      AtomicEvaluationLineageReceipt registry entry

    attributionReference : String

open AttributedAtomicCaseRegistry public

------------------------------------------------------------------------
-- Lineage survives a duplicate registered test because duplication may change
-- only the test object, never the canonical entry or its attribution receipts.
------------------------------------------------------------------------

registeredDuplicateRetainsDefinitionLineage :
  ∀ {registry p} →
  (attributed : AttributedAtomicCaseRegistry registry) →
  (entry : Coherence.Entry registry p) →
  Coherence.RegisteredAtomicTest registry entry →
  Provenance.ClaimLineageReceipt p
registeredDuplicateRetainsDefinitionLineage attributed entry _ =
  definitionLineageFor attributed entry

registeredDuplicateRetainsEntryOutcomeLineage :
  ∀ {registry p} →
  (attributed : AttributedAtomicCaseRegistry registry) →
  (entry : Coherence.Entry registry p) →
  Coherence.RegisteredAtomicTest registry entry →
  AtomicEntryOutcomeLineage registry entry
registeredDuplicateRetainsEntryOutcomeLineage attributed entry _ =
  outcomeLineageFor attributed entry

registeredDuplicateRetainsEvaluationLineage :
  ∀ {registry p} →
  (attributed : AttributedAtomicCaseRegistry registry) →
  (entry : Coherence.Entry registry p) →
  Coherence.RegisteredAtomicTest registry entry →
  AtomicEvaluationLineageReceipt registry entry
registeredDuplicateRetainsEvaluationLineage attributed entry _ =
  evaluationLineageFor attributed entry

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameGateMeansSameProvenanceStage : Set where
data RegistryCoherenceCreatesAttribution : Set where
data DefinitionSourceMayReplaceOutcomeEvidence : Set where
data OutcomeEvidenceMayRedefineLegalTest : Set where
data UnresolvedGateMayInventOutcomeSource : Set where
data RepositoryInferenceMayBePromotedByRegistration : Set where
data PrimarySourceReceiptForcesDefinitionExternalClaim : Set where
data SourceEvidenceOwnsRepositoryGate : Set where

sameGateDoesNotIdentifyProvenanceStage : SameGateMeansSameProvenanceStage → ⊥
sameGateDoesNotIdentifyProvenanceStage ()

registryCoherenceDoesNotCreateAttribution : RegistryCoherenceCreatesAttribution → ⊥
registryCoherenceDoesNotCreateAttribution ()

definitionSourceDoesNotReplaceOutcomeEvidence : DefinitionSourceMayReplaceOutcomeEvidence → ⊥
definitionSourceDoesNotReplaceOutcomeEvidence ()

outcomeEvidenceDoesNotRedefineLegalTest : OutcomeEvidenceMayRedefineLegalTest → ⊥
outcomeEvidenceDoesNotRedefineLegalTest ()

unresolvedGateDoesNotInventOutcomeSource : UnresolvedGateMayInventOutcomeSource → ⊥
unresolvedGateDoesNotInventOutcomeSource ()

registrationDoesNotPromoteRepositoryInference :
  RepositoryInferenceMayBePromotedByRegistration → ⊥
registrationDoesNotPromoteRepositoryInference ()

primarySourceReceiptDoesNotForceDefinitionExternalClaim :
  PrimarySourceReceiptForcesDefinitionExternalClaim → ⊥
primarySourceReceiptDoesNotForceDefinitionExternalClaim ()

sourceEvidenceDoesNotOwnRepositoryGate : SourceEvidenceOwnsRepositoryGate → ⊥
sourceEvidenceDoesNotOwnRepositoryGate ()

record AttributedAtomicCaseRegistryBoundary : Set where
  constructor attributed-atomic-case-registry-boundary
  field
    definitionOutcomeAndEvaluationAttributionSeparated : Bool
    definitionStageIsExplicit : Bool
    everyRegisteredOutcomeCarriesLineageOrExplicitUnresolved : Bool
    everyRegisteredEvaluationCarriesTypedLineage : Bool
    sourceEvidenceOwnsRepositoryGate : Bool
    sameGateIdentifiesProvenance : Bool
    registryCreatesAttribution : Bool
    registrationPromotesInference : Bool

canonicalAttributedAtomicCaseRegistryBoundary :
  AttributedAtomicCaseRegistryBoundary
canonicalAttributedAtomicCaseRegistryBoundary =
  attributed-atomic-case-registry-boundary
    true true true true false false false false
