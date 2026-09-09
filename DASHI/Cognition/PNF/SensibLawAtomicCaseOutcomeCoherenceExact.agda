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
-- SourceConditionedAtomicLegalTest guarantees fit/failure exclusivity inside one
-- test object.  Legal consumers also need a shared case environment so a later
-- rule cannot evade a sourced -1 merely by constructing a fresh +1 test for the
-- same proposition on the same case fibre.
--
-- The environment owns exactly one trit per proposition/context pair.  Tests do
-- not obtain authority from this map: they remain independently source-paid;
-- the map only gives cross-construction outcome coherence.
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

sameCaseNegativePositiveSplitImpossible :
  ∀ {environment context p}
    (left right : ContextBoundAtomicTest environment context p) →
  Atomic.gate (atomicTest left) ≡ BT.neg →
  Atomic.gate (atomicTest right) ≡ BT.pos →
  ⊥
sameCaseNegativePositiveSplitImpossible left right leftNeg rightPos =
  negNotPos
    (trans (sym leftNeg)
      (trans (sameCaseTestsHaveSameGate left right) rightPos))
  where
    negNotPos : BT.neg ≡ BT.pos → ⊥
    negNotPos ()

------------------------------------------------------------------------
-- The environment does NOT make an unresolved atom positive/negative, create
-- source authority, or identify two different propositions that happen to have
-- the same trit.
------------------------------------------------------------------------

data OutcomeEnvironmentCreatesAuthority : Set where
data SameGateMeansSameLegalAtom : Set where
data SameGateMeansSameSourceHistory : Set where
data EnvironmentChangesAtomicSourceReceipt : Set where
data ZeroMayBeSilentlyRefinedWithoutEvidence : Set where

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

record AtomicCaseOutcomeCoherenceBoundary : Set where
  constructor atomic-case-outcome-coherence-boundary
  field
    oneOutcomePerAtomPerCaseEnvironment : Bool
    separateTestObjectsMayContradictWithinSameEnvironment : Bool
    sourceReceiptStillIndependent : Bool
    sameGateIdentifiesLegalAtom : Bool
    environmentCreatesAuthority : Bool

canonicalAtomicCaseOutcomeCoherenceBoundary : AtomicCaseOutcomeCoherenceBoundary
canonicalAtomicCaseOutcomeCoherenceBoundary =
  atomic-case-outcome-coherence-boundary true false true false false
