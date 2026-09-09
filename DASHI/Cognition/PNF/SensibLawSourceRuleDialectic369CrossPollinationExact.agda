module DASHI.Cognition.PNF.SensibLawSourceRuleDialectic369CrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import Base369 as Base
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Ternary
import DASHI.Culture.IntellectualReceptionIntersectionalTernaryDialectic369BridgeExact as Existing369
import DASHI.Culture.PhilosophyClaimProvenanceHistoryBidiExact as Attribution
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule

------------------------------------------------------------------------
-- LEGAL SOURCE-RULE x 369 DIALECTIC CROSS-POLLINATION
--
-- The 369 carrier is used only as an audit geometry.  It does not decide legal
-- truth, authority, applicability or violation.  Its useful contribution is
-- direction-sensitive preservation: support / unresolved / defeat and the
-- ordered relation between positive and negative source branches are retained
-- when a later consumer coordinate is added.
------------------------------------------------------------------------

data LegalSourceDisposition : Set where
  defeats : LegalSourceDisposition
  unresolvedOrQualified : LegalSourceDisposition
  supports : LegalSourceDisposition

dispositionTri : LegalSourceDisposition → Base.TriTruth
dispositionTri defeats = Base.tri-low
dispositionTri unresolvedOrQualified = Base.tri-mid
dispositionTri supports = Base.tri-high

record DirectedSourceRuleAudit : Set where
  constructor directed-source-rule-audit
  field
    positiveBranch : LegalSourceDisposition
    negativeBranch : LegalSourceDisposition
    consumerDisposition : LegalSourceDisposition

open DirectedSourceRuleAudit public

sourceComparison9 : DirectedSourceRuleAudit → Ternary.Comparison9
sourceComparison9 audit =
  dispositionTri (positiveBranch audit) ,
  dispositionTri (negativeBranch audit)

sourceSynthesis27 : DirectedSourceRuleAudit → Ternary.SynthesisChoice27
sourceSynthesis27 audit =
  Ternary.makeSynthesisChoice
    (dispositionTri (positiveBranch audit))
    (dispositionTri (negativeBranch audit))
    (dispositionTri (consumerDisposition audit))

sourceComparisonSurvivesConsumerSynthesis :
  (audit : DirectedSourceRuleAudit) →
  Ternary.comparisonOfSynthesis (sourceSynthesis27 audit)
  ≡ sourceComparison9 audit
sourceComparisonSurvivesConsumerSynthesis audit = refl

------------------------------------------------------------------------
-- Direction matters: support lost and defeater lost are different moves even
-- if a coarse Boolean observer says merely "one source was removed".
------------------------------------------------------------------------

supportLostAudit : DirectedSourceRuleAudit
supportLostAudit = directed-source-rule-audit supports unresolvedOrQualified unresolvedOrQualified

defeaterLostAudit : DirectedSourceRuleAudit
defeaterLostAudit = directed-source-rule-audit unresolvedOrQualified defeats supports

supportLossAndDefeaterLossDiffer :
  sourceComparison9 supportLostAudit ≡ sourceComparison9 defeaterLostAudit → ⊥
supportLossAndDefeaterLossDiffer ()

------------------------------------------------------------------------
-- Existing repository boundaries are reused directly.
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
-- Source lineage is not recoverable from the surviving legal disposition.
------------------------------------------------------------------------

data SameLegalDispositionRestoresSourceHistory : Set where
data TernaryHighMeansLegalTruth : Set where
data TernaryLowMeansLogicalNegation : Set where
data SynthesisCoordinateCreatesLegalAuthority : Set where
data SourceRuleAuditReplacesSourceRealisedRule : Set where

sameDispositionDoesNotRestoreSourceHistory :
  SameLegalDispositionRestoresSourceHistory → ⊥
sameDispositionDoesNotRestoreSourceHistory ()

ternaryHighDoesNotMeanLegalTruth : TernaryHighMeansLegalTruth → ⊥
ternaryHighDoesNotMeanLegalTruth ()

ternaryLowDoesNotMeanLogicalNegation : TernaryLowMeansLogicalNegation → ⊥
ternaryLowDoesNotMeanLogicalNegation ()

synthesisDoesNotCreateAuthority : SynthesisCoordinateCreatesLegalAuthority → ⊥
synthesisDoesNotCreateAuthority ()

auditDoesNotReplaceSourceRealisation :
  SourceRuleAuditReplacesSourceRealisedRule → ⊥
auditDoesNotReplaceSourceRealisation ()

record Legal369CrossPollinationBoundary : Set where
  constructor legal-369-cross-pollination-boundary
  field
    threeWayDispositionRetained : Bool
    orderedPositiveNegativePairRetained : Bool
    consumerCoordinateDoesNotEraseSourcePair : Bool
    sourceAttributionRetained : Bool
    ternaryCarrierCreatesLegalAuthority : Bool
    sourceFilteringAssumedMonotone : Bool

canonicalLegal369CrossPollinationBoundary : Legal369CrossPollinationBoundary
canonicalLegal369CrossPollinationBoundary =
  legal-369-cross-pollination-boundary
    true true true true false false
