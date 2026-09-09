module DASHI.Cognition.PNF.SensibLawAttributedAtomicCaseRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawAtomicCaseOutcomeCoherenceExact as Coherence
import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Provenance

------------------------------------------------------------------------
-- ATTRIBUTED ATOMIC CASE REGISTRY
--
-- An atomic legal test has two independent attribution fibres:
--   1. the source defining/owning the legal test proposition;
--   2. the provenance of the concrete case outcome evidence.
--
-- Registration/coherence must preserve both.  A gate is not a provenance tag.
------------------------------------------------------------------------

definitionLineage :
  (registry : Coherence.AtomicCaseRegistry) →
  ∀ {p} →
  (entry : Coherence.Entry registry p) →
  Provenance.ClaimLineageReceipt p
definitionLineage registry entry =
  Provenance.lineageFromPropositionSourceReceipt
    (Atomic.sourceReceipt (Coherence.canonicalTestFor registry entry))

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

record AttributedAtomicCaseRegistry
    (registry : Coherence.AtomicCaseRegistry) : Set₁ where
  constructor attributed-atomic-case-registry
  field
    outcomeLineageFor :
      ∀ {p} →
      (entry : Coherence.Entry registry p) →
      AtomicEntryOutcomeLineage registry entry
    attributionReference : String

open AttributedAtomicCaseRegistry public

------------------------------------------------------------------------
-- Lineage survives a duplicate registered test because duplication may change
-- only the test object, never the canonical registry entry or its attribution.
------------------------------------------------------------------------

registeredDuplicateRetainsEntryOutcomeLineage :
  ∀ {registry p} →
  (attributed : AttributedAtomicCaseRegistry registry) →
  (entry : Coherence.Entry registry p) →
  Coherence.RegisteredAtomicTest registry entry →
  AtomicEntryOutcomeLineage registry entry
registeredDuplicateRetainsEntryOutcomeLineage attributed entry _ =
  outcomeLineageFor attributed entry

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameGateMeansSameProvenanceStage : Set where
data RegistryCoherenceCreatesAttribution : Set where
data DefinitionSourceMayReplaceOutcomeEvidence : Set where
data OutcomeEvidenceMayRedefineLegalTest : Set where
data UnresolvedGateMayInventOutcomeSource : Set where
data RepositoryInferenceMayBePromotedByRegistration : Set where

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

record AttributedAtomicCaseRegistryBoundary : Set where
  constructor attributed-atomic-case-registry-boundary
  field
    definitionAndOutcomeAttributionSeparated : Bool
    everyRegisteredOutcomeCarriesLineageOrExplicitUnresolved : Bool
    sameGateIdentifiesProvenance : Bool
    registryCreatesAttribution : Bool
    registrationPromotesInference : Bool

canonicalAttributedAtomicCaseRegistryBoundary :
  AttributedAtomicCaseRegistryBoundary
canonicalAttributedAtomicCaseRegistryBoundary =
  attributed-atomic-case-registry-boundary true true false false false
