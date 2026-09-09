module DASHI.Cognition.PNF.SensibLawSourceRuleDialectic369CrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import Base369 as Base
import DASHI.Algebra.BalancedTernary as BT
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Ternary
import DASHI.Culture.IntellectualReceptionIntersectionalTernaryDialectic369BridgeExact as Existing369
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic

data AtomicFitDisposition : Set where
  failsThisAtom : AtomicFitDisposition
  unresolvedThisAtom : AtomicFitDisposition
  fitsThisAtom : AtomicFitDisposition

atomicFitDispositionFromGate : BT.Trit → AtomicFitDisposition
atomicFitDispositionFromGate BT.neg = failsThisAtom
atomicFitDispositionFromGate BT.zero = unresolvedThisAtom
atomicFitDispositionFromGate BT.pos = fitsThisAtom

atomicDispositionTri : AtomicFitDisposition → Base.TriTruth
atomicDispositionTri failsThisAtom = Base.tri-low
atomicDispositionTri unresolvedThisAtom = Base.tri-mid
atomicDispositionTri fitsThisAtom = Base.tri-high

atomicGateTri : BT.Trit → Base.TriTruth
atomicGateTri gate = atomicDispositionTri (atomicFitDispositionFromGate gate)

atomicGateNegIsLow : atomicGateTri BT.neg ≡ Base.tri-low
atomicGateNegIsLow = refl

atomicGateZeroIsMid : atomicGateTri BT.zero ≡ Base.tri-mid
atomicGateZeroIsMid = refl

atomicGatePosIsHigh : atomicGateTri BT.pos ≡ Base.tri-high
atomicGatePosIsHigh = refl

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
  Ternary.comparisonOfSynthesis (sourceSynthesis27 audit) ≡ sourceComparison9 audit
sourceComparisonSurvivesConsumerSynthesis audit = refl

atomicTestsTo27 :
  ∀ {p q r} →
  Atomic.SourceConditionedAtomicLegalTest p →
  Atomic.SourceConditionedAtomicLegalTest q →
  Atomic.SourceConditionedAtomicLegalTest r →
  Ternary.SynthesisChoice27
atomicTestsTo27 p q r = Ternary.makeSynthesisChoice
  (atomicGateTri (Atomic.gate p))
  (atomicGateTri (Atomic.gate q))
  (atomicGateTri (Atomic.gate r))

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

binaryProjectionCanEraseDirection : Existing369.BinaryInteractionIsCompleteTernarySemantics → ⊥
binaryProjectionCanEraseDirection = Existing369.binaryInteractionDoesNotCompleteTernarySemantics

historicalOrLegalOppositionIsNotLogicalNegation :
  Existing369.BinaryInteractionIsCompleteDialecticSemantics → ⊥
historicalOrLegalOppositionIsNotLogicalNegation = Existing369.binaryInteractionDoesNotCompleteDialecticSemantics

sourceAttributionMustSurviveCrossPollination : Bool
sourceAttributionMustSurviveCrossPollination =
  Existing369.IntellectualReceptionIntersectionalTernaryDialectic369Boundary.sourceAttributionBoundarySurvives
    Existing369.canonicalIntellectualReceptionIntersectionalTernaryDialectic369Boundary

sourceAttributionMustSurviveCrossPollinationIsTrue : sourceAttributionMustSurviveCrossPollination ≡ true
sourceAttributionMustSurviveCrossPollinationIsTrue = refl

data SameAtomicDispositionRestoresSourceHistory : Set where
data TernaryHighMeansLegalTruth : Set where
data TernaryLowMeansOppositeLegalProposition : Set where
data SynthesisCoordinateCreatesLegalAuthority : Set where
data AtomicAuditReplacesSourceConditionedTest : Set where

data HandEntered369LabelReplacesAtomicGate : Set where

sameAtomicDispositionDoesNotRestoreSourceHistory : SameAtomicDispositionRestoresSourceHistory → ⊥
sameAtomicDispositionDoesNotRestoreSourceHistory ()
ternaryHighDoesNotMeanLegalTruth : TernaryHighMeansLegalTruth → ⊥
ternaryHighDoesNotMeanLegalTruth ()
ternaryLowDoesNotMeanOppositeLegalProposition : TernaryLowMeansOppositeLegalProposition → ⊥
ternaryLowDoesNotMeanOppositeLegalProposition ()
synthesisDoesNotCreateAuthority : SynthesisCoordinateCreatesLegalAuthority → ⊥
synthesisDoesNotCreateAuthority ()
auditDoesNotReplaceAtomicTest : AtomicAuditReplacesSourceConditionedTest → ⊥
auditDoesNotReplaceAtomicTest ()
handEntered369DoesNotReplaceAtomicGate : HandEntered369LabelReplacesAtomicGate → ⊥
handEntered369DoesNotReplaceAtomicGate ()

atomicNegativeBoundaryReused : Atomic.NegativeGateProvesOppositeProposition → ⊥
atomicNegativeBoundaryReused = Atomic.negativeGateDoesNotProveOppositeProposition

record Legal369CrossPollinationBoundary : Set where
  constructor legal-369-cross-pollination-boundary
  field
    canonicalAtomicGateDrives369Audit : Bool
    threeWayAtomicFitDispositionRetained : Bool
    orderedPositiveNegativePairRetained : Bool
    consumerCoordinateDoesNotEraseSourcePair : Bool
    sourceAttributionRetained : Bool
    negativeMeansFailureOfSameAtom : Bool
    negativeMeansOppositeLegalProposition : Bool
    ternaryCarrierCreatesLegalAuthority : Bool

canonicalLegal369CrossPollinationBoundary : Legal369CrossPollinationBoundary
canonicalLegal369CrossPollinationBoundary =
  legal-369-cross-pollination-boundary true true true true true true false false
