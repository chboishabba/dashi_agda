module DASHI.Cognition.PNF.SensibLawSourceRuleDialectic369CrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import Base369 as Base
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Ternary
import DASHI.Culture.IntellectualReceptionIntersectionalTernaryDialectic369BridgeExact as Existing369
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic

------------------------------------------------------------------------
-- LEGAL SOURCE-RULE x 369 DIALECTIC CROSS-POLLINATION
--
-- The 369 carrier is audit geometry only.  Each ternary coordinate is the fit
-- state of ONE declared legal atom:
--
--   tri-low  = positive witness that this atom fails its test
--   tri-mid  = this atom is unresolved / not yet bound
--   tri-high = positive witness that this atom fits its test
--
-- `tri-low` therefore never means the logical/lexical opposite proposition.
-- The ordered pair retains direction when a later consumer coordinate is added.
------------------------------------------------------------------------

data AtomicFitDisposition : Set where
  failsThisAtom : AtomicFitDisposition
  unresolvedThisAtom : AtomicFitDisposition
  fitsThisAtom : AtomicFitDisposition

atomicDispositionTri : AtomicFitDisposition → Base.TriTruth
atomicDispositionTri failsThisAtom = Base.tri-low
atomicDispositionTri unresolvedThisAtom = Base.tri-mid
atomicDispositionTri fitsThisAtom = Base.tri-high

record DirectedAtomicRuleAudit : Set where
  constructor directed-atomic-rule-audit
  field
    positiveRequirementAtom : AtomicFitDisposition
    exceptionOrDefeaterAtom : AtomicFitDisposition
    consumerAtom : AtomicFitDisposition

open DirectedAtomicRuleAudit public

sourceComparison9 : DirectedAtomicRuleAudit → Ternary.Comparison9
sourceComparison9 audit =
  atomicDispositionTri (positiveRequirementAtom audit) ,
  atomicDispositionTri (exceptionOrDefeaterAtom audit)

sourceSynthesis27 : DirectedAtomicRuleAudit → Ternary.SynthesisChoice27
sourceSynthesis27 audit =
  Ternary.makeSynthesisChoice
    (atomicDispositionTri (positiveRequirementAtom audit))
    (atomicDispositionTri (exceptionOrDefeaterAtom audit))
    (atomicDispositionTri (consumerAtom audit))

sourceComparisonSurvivesConsumerSynthesis :
  (audit : DirectedAtomicRuleAudit) →
  Ternary.comparisonOfSynthesis (sourceSynthesis27 audit)
  ≡ sourceComparison9 audit
sourceComparisonSurvivesConsumerSynthesis audit = refl

------------------------------------------------------------------------
-- Direction matters.  Losing support for a positive requirement and losing an
-- exception/defeater are different atomic changes even if a Boolean observer
-- reports only "one source/test changed".
------------------------------------------------------------------------

positiveRequirementLostAudit : DirectedAtomicRuleAudit
positiveRequirementLostAudit =
  directed-atomic-rule-audit fitsThisAtom unresolvedThisAtom unresolvedThisAtom

negativeBranchFailsToApplyAudit : DirectedAtomicRuleAudit
negativeBranchFailsToApplyAudit =
  directed-atomic-rule-audit unresolvedThisAtom failsThisAtom fitsThisAtom

positiveLossAndNegativeFailureDiffer :
  sourceComparison9 positiveRequirementLostAudit
  ≡ sourceComparison9 negativeBranchFailsToApplyAudit → ⊥
positiveLossAndNegativeFailureDiffer ()

------------------------------------------------------------------------
-- Existing repository 369 boundaries are reused directly.
------------------------------------------------------------------------

binaryProjectionCanEraseDirection :
  Existing369.BinaryInteractionIsCompleteTernarySemantics → ⊥
binaryProjectionCanEraseDirection =
  Existing369.binaryInteractionDoesNotCompleteTernarySemantics

historicalOrLegalOppositionIsNotLogicalNegation :
  Existing369.BinaryInteractionIsCompleteDialecticSemantics → ⊥
historicalOrLegalOppositionIsNotLogicalNegation =
  Existing369.binaryInteractionDoesNotCompleteDialecticSemantics

sourceAttributionMustSurviveCrossPollination : Bool
sourceAttributionMustSurviveCrossPollination =
  Existing369.IntellectualReceptionIntersectionalTernaryDialectic369Boundary.sourceAttributionBoundarySurvives
    Existing369.canonicalIntellectualReceptionIntersectionalTernaryDialectic369Boundary

sourceAttributionMustSurviveCrossPollinationIsTrue :
  sourceAttributionMustSurviveCrossPollination ≡ true
sourceAttributionMustSurviveCrossPollinationIsTrue = refl

------------------------------------------------------------------------
-- Atomic no-collapse laws.
------------------------------------------------------------------------

data SameAtomicDispositionRestoresSourceHistory : Set where
data TernaryHighMeansLegalTruth : Set where
data TernaryLowMeansOppositeLegalProposition : Set where
data SynthesisCoordinateCreatesLegalAuthority : Set where
data AtomicAuditReplacesSourceConditionedTest : Set where

sameAtomicDispositionDoesNotRestoreSourceHistory :
  SameAtomicDispositionRestoresSourceHistory → ⊥
sameAtomicDispositionDoesNotRestoreSourceHistory ()

ternaryHighDoesNotMeanLegalTruth : TernaryHighMeansLegalTruth → ⊥
ternaryHighDoesNotMeanLegalTruth ()

ternaryLowDoesNotMeanOppositeLegalProposition :
  TernaryLowMeansOppositeLegalProposition → ⊥
ternaryLowDoesNotMeanOppositeLegalProposition ()

synthesisDoesNotCreateAuthority : SynthesisCoordinateCreatesLegalAuthority → ⊥
synthesisDoesNotCreateAuthority ()

auditDoesNotReplaceAtomicTest : AtomicAuditReplacesSourceConditionedTest → ⊥
auditDoesNotReplaceAtomicTest ()

atomicNegativeBoundaryReused : Atomic.NegativeGateProvesOppositeProposition → ⊥
atomicNegativeBoundaryReused = Atomic.negativeGateDoesNotProveOppositeProposition

record Legal369CrossPollinationBoundary : Set where
  constructor legal-369-cross-pollination-boundary
  field
    threeWayAtomicFitDispositionRetained : Bool
    orderedPositiveNegativePairRetained : Bool
    consumerCoordinateDoesNotEraseSourcePair : Bool
    sourceAttributionRetained : Bool
    negativeMeansFailureOfSameAtom : Bool
    negativeMeansOppositeLegalProposition : Bool
    ternaryCarrierCreatesLegalAuthority : Bool

canonicalLegal369CrossPollinationBoundary : Legal369CrossPollinationBoundary
canonicalLegal369CrossPollinationBoundary =
  legal-369-cross-pollination-boundary
    true true true true true false false
