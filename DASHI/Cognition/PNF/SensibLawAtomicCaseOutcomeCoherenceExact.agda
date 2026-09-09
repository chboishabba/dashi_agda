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

------------------------------------------------------------------------
-- ATOMIC SAME-CASE OUTCOME COHERENCE
--
-- One atomic test object is internally exclusive, but without a cross-object
-- coherence receipt a later consumer could manufacture a fresh +1 test for a
-- proposition already sourced as -1 on the same case fibre.  This module owns
-- that missing coherence coordinate.
------------------------------------------------------------------------

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
-- Finite registry surface.
--
-- Most legal applications should not invent an outcome for every proposition in
-- the legal universe.  A finite registry instead lists only the atoms actually
-- evaluated on the retained case fibre.  Each entry owns one canonical sourced
-- test; any consumer-created duplicate must prove gate equality to that entry.
------------------------------------------------------------------------

record AtomicCaseRegistry : Set₁ where
  constructor atomic-case-registry
  field
    Entry : Set
    propositionFor : Entry → Algebra.LegalProposition
    contextFor : Entry → Ontology.StableId
    canonicalTestFor :
      (entry : Entry) →
      Atomic.SourceConditionedAtomicLegalTest (propositionFor entry)
    registryReference : String

open AtomicCaseRegistry public

record RegisteredAtomicTest
    (registry : AtomicCaseRegistry)
    (entry : Entry registry) : Set₁ where
  constructor registered-atomic-test
  field
    candidateTest :
      Atomic.SourceConditionedAtomicLegalTest (propositionFor registry entry)
    gateMatchesCanonical :
      Atomic.gate candidateTest
      ≡ Atomic.gate (canonicalTestFor registry entry)
    registrationReference : String

open RegisteredAtomicTest public

canonicalRegisteredAtomicTest :
  (registry : AtomicCaseRegistry) →
  (entry : Entry registry) →
  RegisteredAtomicTest registry entry
canonicalRegisteredAtomicTest registry entry =
  registered-atomic-test
    (canonicalTestFor registry entry)
    refl
    "canonical registered atomic test"

registeredTestsHaveSameGate :
  ∀ {registry entry}
    (left right : RegisteredAtomicTest registry entry) →
  Atomic.gate (candidateTest left) ≡ Atomic.gate (candidateTest right)
registeredTestsHaveSameGate left right =
  trans (gateMatchesCanonical left) (sym (gateMatchesCanonical right))

registeredNegativeCannotBeReintroducedPositive :
  ∀ {registry entry}
    (canonicalNegative :
      Atomic.gate (canonicalTestFor registry entry) ≡ BT.neg) →
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
  ∀ {registry entry}
    (canonicalPositive :
      Atomic.gate (canonicalTestFor registry entry) ≡ BT.pos) →
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
    oneOutcomePerRegisteredAtomPerCase : Bool
    finiteRegistryAvoidsInventedUniverseOutcomes : Bool
    separateRegisteredTestsMayContradict : Bool
    sourceReceiptStillIndependent : Bool
    sameGateIdentifiesLegalAtom : Bool
    registryCreatesAuthority : Bool

canonicalAtomicCaseOutcomeCoherenceBoundary : AtomicCaseOutcomeCoherenceBoundary
canonicalAtomicCaseOutcomeCoherenceBoundary =
  atomic-case-outcome-coherence-boundary true true false true false false
