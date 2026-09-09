module DASHI.Cognition.PNF.SensibLawAtomicCaseOutcomeCoherenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic

record AtomicCaseOutcomeEnvironment : Set₁ where
  constructor atomic-case-outcome-environment
  field
    outcome : Algebra.LegalProposition → Ontology.StableId → BT.Trit
    environmentReference : String

open AtomicCaseOutcomeEnvironment public

record ContextBoundAtomicTest
    (environment : AtomicCaseOutcomeEnvironment)
    (context : Ontology.StableId)
    (p : Algebra.LegalProposition) : Set₁ where
  constructor context-bound-atomic-test
  field
    atomicTest : Atomic.SourceConditionedAtomicLegalTest p
    gateMatchesEnvironment :
      Atomic.gate atomicTest ≡ outcome environment p context
    contextReference : String

open ContextBoundAtomicTest public

sameCaseTestsHaveSameGate :
  ∀ {environment context p}
    (left right : ContextBoundAtomicTest environment context p) →
  Atomic.gate (atomicTest left) ≡ Atomic.gate (atomicTest right)
sameCaseTestsHaveSameGate left right =
  trans (gateMatchesEnvironment left) (sym (gateMatchesEnvironment right))

sameCasePositiveNegativeSplitImpossible :
  ∀ {environment context p}
    (left right : ContextBoundAtomicTest environment context p) →
  Atomic.gate (atomicTest left) ≡ BT.pos →
  Atomic.gate (atomicTest right) ≡ BT.neg →
  ⊥
sameCasePositiveNegativeSplitImpossible left right leftPos rightNeg =
  posNotNeg
    (trans (sym leftPos)
      (trans (sameCaseTestsHaveSameGate left right) rightNeg))
  where
    posNotNeg : BT.pos ≡ BT.neg → ⊥
    posNotNeg ()

------------------------------------------------------------------------
-- Atomic finite registry.
--
-- Entry is indexed by the exact proposition, so there is no separate
-- propositionFor field/equality seam.  Each registered atom has one canonical
-- source-conditioned test on one retained case context.
------------------------------------------------------------------------

record AtomicCaseRegistry : Set₁ where
  constructor atomic-case-registry
  field
    Entry : Algebra.LegalProposition → Set
    contextFor :
      ∀ {p} → Entry p → Ontology.StableId
    canonicalTestFor :
      ∀ {p} → (entry : Entry p) →
      Atomic.SourceConditionedAtomicLegalTest p
    registryReference : String

open AtomicCaseRegistry public

record RegisteredAtomicTest
    (registry : AtomicCaseRegistry)
    {p : Algebra.LegalProposition}
    (entry : Entry registry p) : Set₁ where
  constructor registered-atomic-test
  field
    candidateTest : Atomic.SourceConditionedAtomicLegalTest p
    gateMatchesCanonical :
      Atomic.gate candidateTest
      ≡ Atomic.gate (canonicalTestFor registry entry)
    registrationReference : String

open RegisteredAtomicTest public

canonicalRegisteredAtomicTest :
  (registry : AtomicCaseRegistry) →
  ∀ {p} →
  (entry : Entry registry p) →
  RegisteredAtomicTest registry entry
canonicalRegisteredAtomicTest registry entry =
  registered-atomic-test
    (canonicalTestFor registry entry)
    refl
    "canonical registered atomic test"

registeredTestsHaveSameGate :
  ∀ {registry p} {entry : Entry registry p}
    (left right : RegisteredAtomicTest registry entry) →
  Atomic.gate (candidateTest left) ≡ Atomic.gate (candidateTest right)
registeredTestsHaveSameGate left right =
  trans (gateMatchesCanonical left) (sym (gateMatchesCanonical right))

registeredNegativeCannotBeReintroducedPositive :
  ∀ {registry p} {entry : Entry registry p} →
  Atomic.gate (canonicalTestFor registry entry) ≡ BT.neg →
  (candidate : RegisteredAtomicTest registry entry) →
  Atomic.gate (candidateTest candidate) ≡ BT.pos →
  ⊥
registeredNegativeCannotBeReintroducedPositive canonicalNegative candidate candidatePositive =
  negNotPos
    (trans (sym canonicalNegative)
      (trans (sym (gateMatchesCanonical candidate)) candidatePositive))
  where
    negNotPos : BT.neg ≡ BT.pos → ⊥
    negNotPos ()

registeredPositiveCannotBeReintroducedNegative :
  ∀ {registry p} {entry : Entry registry p} →
  Atomic.gate (canonicalTestFor registry entry) ≡ BT.pos →
  (candidate : RegisteredAtomicTest registry entry) →
  Atomic.gate (candidateTest candidate) ≡ BT.neg →
  ⊥
registeredPositiveCannotBeReintroducedNegative canonicalPositive candidate candidateNegative =
  posNotNeg
    (trans (sym canonicalPositive)
      (trans (sym (gateMatchesCanonical candidate)) candidateNegative))
  where
    posNotNeg : BT.pos ≡ BT.neg → ⊥
    posNotNeg ()

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OutcomeEnvironmentCreatesAuthority : Set where
data SameGateMeansSameLegalAtom : Set where
data SameGateMeansSameSourceHistory : Set where
data EnvironmentChangesAtomicSourceReceipt : Set where
data ZeroMayBeSilentlyRefinedWithoutEvidence : Set where
data RegistryEntryCreatesSourceAuthority : Set where
data UnregisteredDuplicateMayOverrideRegisteredOutcome : Set where

outcomeEnvironmentDoesNotCreateAuthority : OutcomeEnvironmentCreatesAuthority → ⊥
outcomeEnvironmentDoesNotCreateAuthority ()

sameGateDoesNotIdentifyLegalAtom : SameGateMeansSameLegalAtom → ⊥
sameGateDoesNotIdentifyLegalAtom ()

sameGateDoesNotRestoreSourceHistory : SameGateMeansSameSourceHistory → ⊥
sameGateDoesNotRestoreSourceHistory ()

environmentDoesNotReplaceSourceReceipt : EnvironmentChangesAtomicSourceReceipt → ⊥
environmentDoesNotReplaceSourceReceipt ()

zeroCannotBeRefinedWithoutNewEvidence : ZeroMayBeSilentlyRefinedWithoutEvidence → ⊥
zeroCannotBeRefinedWithoutNewEvidence ()

registryDoesNotCreateAuthority : RegistryEntryCreatesSourceAuthority → ⊥
registryDoesNotCreateAuthority ()

unregisteredDuplicateCannotOverrideByPermission :
  UnregisteredDuplicateMayOverrideRegisteredOutcome → ⊥
unregisteredDuplicateCannotOverrideByPermission ()

record AtomicCaseOutcomeCoherenceBoundary : Set where
  constructor atomic-case-outcome-coherence-boundary
  field
    entriesIndexedByExactLegalAtom : Bool
    oneOutcomePerRegisteredAtomPerCase : Bool
    finiteRegistryAvoidsInventedUniverseOutcomes : Bool
    separateRegisteredTestsMayContradict : Bool
    sourceReceiptStillIndependent : Bool
    registryCreatesAuthority : Bool

canonicalAtomicCaseOutcomeCoherenceBoundary : AtomicCaseOutcomeCoherenceBoundary
canonicalAtomicCaseOutcomeCoherenceBoundary =
  atomic-case-outcome-coherence-boundary true true true false true false
