module DASHI.Reasoning.Spacy369FeministLacanConsumerRelativeExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.FeministRechartingSourceBridgeExact as Rechart
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact as LI
import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Reasoning.SemanticCandidateResidualBidiExact as Semantic
import DASHI.Reasoning.SemanticConsumerRelativeClosureExact as Closure
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SpacyPNF369DialecticBridgeExact as Bridge369
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace

open Candidate using (Formula; notF; _∨_)

------------------------------------------------------------------------
-- MATERIALISED SPACY / 369 / FEMINIST / LACAN CONSUMER-RELATIVE BRIDGE
--
-- This owner starts from the real SensibLaw spaCy fixture already materialised
-- by SpacyNegatedCoordinationScopeTraceExact.  The broad and narrow scope
-- readings remain live semantic candidates.  Different downstream consumers
-- may nevertheless require different amounts of refinement.
--
-- Feminist/Lacanian material enters only as typed audit/recharting structure:
--   * utterance/parse visibility does not recover originating subject position;
--   * positive recharting adds a residual coordinate rather than relabelling;
--   * a shared ternary carrier does not identify Lacanian and Irigarayan
--     relational grammars.
--
-- Nothing here attributes parser semantics, PNF logic, or the finite DASHI
-- non-factorability theorem to Lacan, Irigaray, or feminist sources.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. One operational consumer is already closed across the real broad/narrow
--    semantic fibre.
------------------------------------------------------------------------

data OperationalDecision : Set where
  noAutomaticStateMutation : OperationalDecision

operationalConsumer : Candidate.CandidateSemanticFragment → OperationalDecision
operationalConsumer fragment = noAutomaticStateMutation

operationalConsumerClosedOnMaterialisedFibre :
  Closure.ConsumerClosedOnSemanticFibre Trace.candidateFibre operationalConsumer
operationalConsumerClosedOnMaterialisedFibre left right leftLive rightLive = refl

operationalClosureReceipt :
  Closure.SemanticConsumerClosure Trace.candidateFibre operationalConsumer
operationalClosureReceipt =
  Closure.semanticConsumerClosure
    operationalConsumerClosedOnMaterialisedFibre
    "consumer: runtime must not automatically mutate/promote from this sentence"
    "broad/narrow scope ambiguity is irrelevant to this declared operational decision"
    "semantic scope alternatives remain retained"

------------------------------------------------------------------------
-- 2. A scope-sensitive consumer is NOT closed on the same live fibre.
------------------------------------------------------------------------

data ScopeDecision : Set where
  broadScopeDecision narrowScopeDecision otherScopeDecision : ScopeDecision

scopeConsumer : Candidate.CandidateSemanticFragment → ScopeDecision
scopeConsumer fragment with Candidate.formula fragment
... | notF (_ ∨ _) = broadScopeDecision
... | notF _ = narrowScopeDecision
... | _ = otherScopeDecision

broadScopeDecisionNotNarrow : broadScopeDecision ≡ narrowScopeDecision → ⊥
broadScopeDecisionNotNarrow ()

scopeSensitiveConsumerNotClosed :
  Closure.ConsumerClosedOnSemanticFibre Trace.candidateFibre scopeConsumer → ⊥
scopeSensitiveConsumerNotClosed closed =
  broadScopeDecisionNotNarrow
    (closed
      Trace.negBroadCandidate
      Trace.negNarrowCandidate
      Semantic.here
      (Semantic.there Semantic.here))

------------------------------------------------------------------------
-- 3. Feminist subject-position cross-pollination.
--
-- Two fine situated states can expose the SAME parser candidate and SAME 369
-- review atom while differing on originating/represented subject position.
-- Thus parser/369 closure for an operational consumer is not automatically
-- closure for a subject-position-sensitive consumer.
------------------------------------------------------------------------

data SituatedSpacyReading : Set where
  representedReading originatingReading : SituatedSpacyReading

parserSemanticSurface :
  SituatedSpacyReading → Candidate.CandidateSemanticFragment
parserSemanticSurface representedReading = Trace.negNarrowCandidate
parserSemanticSurface originatingReading = Trace.negNarrowCandidate

dialectic369Surface :
  SituatedSpacyReading → Bridge369.SpacyCandidateDialectic369Atom
dialectic369Surface representedReading = Trace.revised369
dialectic369Surface originatingReading = Trace.revised369

subjectPositionResidual : SituatedSpacyReading → Subject.SubjectPosition
subjectPositionResidual representedReading = Subject.representedPosition
subjectPositionResidual originatingReading = Subject.originatingPosition

subjectPositionsDiffer :
  subjectPositionResidual representedReading
  ≡ subjectPositionResidual originatingReading → ⊥
subjectPositionsDiffer ()

parserSubjectPositionCollision :
  INF.NonFactorabilityWitness parserSemanticSurface subjectPositionResidual
parserSubjectPositionCollision =
  INF.nonFactorabilityWitness
    representedReading
    originatingReading
    refl
    subjectPositionsDiffer

parserSurfaceCannotRecoverSubjectPosition :
  INF.FactorsThrough parserSemanticSurface subjectPositionResidual → ⊥
parserSurfaceCannotRecoverSubjectPosition =
  INF.witnessRulesOutEveryFlatFactorisation parserSubjectPositionCollision

chart369SubjectPositionCollision :
  INF.NonFactorabilityWitness dialectic369Surface subjectPositionResidual
chart369SubjectPositionCollision =
  INF.nonFactorabilityWitness
    representedReading
    originatingReading
    refl
    subjectPositionsDiffer

chart369CannotRecoverSubjectPosition :
  INF.FactorsThrough dialectic369Surface subjectPositionResidual → ⊥
chart369CannotRecoverSubjectPosition =
  INF.witnessRulesOutEveryFlatFactorisation chart369SubjectPositionCollision

------------------------------------------------------------------------
-- 4. Positive feminist recharting: add the missing residual coordinate.
--    This is not a sign flip or relabel of the parser/369 quotient.
------------------------------------------------------------------------

parserSubjectPositiveRecharting : Rechart.PositiveRecharting parserSemanticSurface
parserSubjectPositiveRecharting =
  Rechart.positive-recharting
    subjectPositionResidual
    representedReading
    originatingReading
    refl
    subjectPositionsDiffer

parserSubjectRechartIsStrict :
  Observer.StrictRefinement
    parserSemanticSurface
    (Observer.pairObserver parserSemanticSurface subjectPositionResidual)
parserSubjectRechartIsStrict =
  Rechart.positiveRechartingStrictlyRefinesInheritedChart
    parserSubjectPositiveRecharting

chart369SubjectPositiveRecharting : Rechart.PositiveRecharting dialectic369Surface
chart369SubjectPositiveRecharting =
  Rechart.positive-recharting
    subjectPositionResidual
    representedReading
    originatingReading
    refl
    subjectPositionsDiffer

chart369SubjectRechartIsStrict :
  Observer.StrictRefinement
    dialectic369Surface
    (Observer.pairObserver dialectic369Surface subjectPositionResidual)
chart369SubjectRechartIsStrict =
  Rechart.positiveRechartingStrictlyRefinesInheritedChart
    chart369SubjectPositiveRecharting

------------------------------------------------------------------------
-- 5. Lacan/Irigaray carrier/grammar boundary.
--
-- The spaCy 369 review chart may use a ternary carrier, but no permutation of
-- that shared carrier supplies a grammar-preserving identification between the
-- finite Lacanian One-centred comparison graph and the Irigarayan reciprocal
-- graph.  Therefore a parser disposition trit has no universal philosophical
-- role semantics.
------------------------------------------------------------------------

sharedTernaryCarrierDoesNotIdentifyLacanIrigarayGrammar :
  (permutation : Ternary.TernaryPermutation) →
  LI.GrammarPreserving permutation → ⊥
sharedTernaryCarrierDoesNotIdentifyLacanIrigarayGrammar =
  LI.noTernaryRelabellingPreservesGrammar

------------------------------------------------------------------------
-- 6. Consumer-relative synthesis of the cross-pollination.
------------------------------------------------------------------------

record Spacy369FeministLacanConsumerBoundary : Set where
  constructor spacy369FeministLacanConsumerBoundary
  field
    operationalConsumerMayCloseBeforeScopeResolution : Bool
    operationalConsumerMayCloseBeforeScopeResolutionIsTrue :
      operationalConsumerMayCloseBeforeScopeResolution ≡ true
    everyConsumerClosesWhenOperationalConsumerCloses : Bool
    everyConsumerClosesWhenOperationalConsumerClosesIsFalse :
      everyConsumerClosesWhenOperationalConsumerCloses ≡ false
    parserSurfaceRecoversOriginatingSubjectPosition : Bool
    parserSurfaceRecoversOriginatingSubjectPositionIsFalse :
      parserSurfaceRecoversOriginatingSubjectPosition ≡ false
    chart369RecoversOriginatingSubjectPosition : Bool
    chart369RecoversOriginatingSubjectPositionIsFalse :
      chart369RecoversOriginatingSubjectPosition ≡ false
    positiveFeministRepairMayAddResidualCoordinate : Bool
    positiveFeministRepairMayAddResidualCoordinateIsTrue :
      positiveFeministRepairMayAddResidualCoordinate ≡ true
    positiveFeministRepairIsSignFlipInsideCollapsedChart : Bool
    positiveFeministRepairIsSignFlipInsideCollapsedChartIsFalse :
      positiveFeministRepairIsSignFlipInsideCollapsedChart ≡ false
    sharedTernaryCarrierMeansSharedLacanIrigarayGrammar : Bool
    sharedTernaryCarrierMeansSharedLacanIrigarayGrammarIsFalse :
      sharedTernaryCarrierMeansSharedLacanIrigarayGrammar ≡ false
    philosophicalAuditCreatesParserWorldFact : Bool
    philosophicalAuditCreatesParserWorldFactIsFalse :
      philosophicalAuditCreatesParserWorldFact ≡ false

canonicalSpacy369FeministLacanConsumerBoundary :
  Spacy369FeministLacanConsumerBoundary
canonicalSpacy369FeministLacanConsumerBoundary =
  spacy369FeministLacanConsumerBoundary
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl
