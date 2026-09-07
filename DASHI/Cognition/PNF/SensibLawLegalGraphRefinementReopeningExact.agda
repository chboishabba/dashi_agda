module DASHI.Cognition.PNF.SensibLawLegalGraphRefinementReopeningExact where

------------------------------------------------------------------------
-- LEGAL GRAPH REFINEMENT / RE-RUN / NON-MONOTONICITY
--
-- Structural module only. No new external legal proposition is introduced.
-- Source-bearing additions must arrive as Algebra.LegalRule / LegalSourceRef /
-- LegalProposition values whose provenance is owned by source-specific modules.
--
-- A crucial legal feature is explicit here: adding information is not generally
-- monotone for derivability because newly observed exceptions or defeaters can
-- invalidate a previously available rule path. Refinement therefore triggers a
-- re-run; it does not merely union conclusions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Core.EpistemicCompressionDeliberativeReopeningBidiExact as CoreReopen

------------------------------------------------------------------------
-- Append-only carrier refinement: old source/rule/fact objects remain
-- addressable. This is provenance preservation, not preservation of all old
-- legal conclusions.
------------------------------------------------------------------------

record GraphRefinement
  (oldGraph newGraph : Algebra.LegalGraph)
  : Set where
  constructor graph-refinement
  field
    oldRulePreserved :
      ∀ {r} → Algebra._∈_ r (Algebra.rules oldGraph) →
      Algebra._∈_ r (Algebra.rules newGraph)
    oldSourcePreserved :
      ∀ {s} → Algebra._∈_ s (Algebra.sourceUniverse oldGraph) →
      Algebra._∈_ s (Algebra.sourceUniverse newGraph)
    addedRuleReference : String
    addedSourceReference : String

open GraphRefinement public

record FactRefinement
  (oldFacts newFacts : Algebra.FactSet)
  : Set where
  constructor fact-refinement
  field
    oldFactPreserved :
      ∀ {p} → Algebra._∈_ p (Algebra.facts oldFacts) →
      Algebra._∈_ p (Algebra.facts newFacts)
    addedFactReference : String

open FactRefinement public

------------------------------------------------------------------------
-- A refinement bundle records which missing legal coordinate motivated the
-- acquisition and which carrier was enriched.
------------------------------------------------------------------------

data RefinementCarrier : Set where
  ruleCarrier : RefinementCarrier
  sourceCarrier : RefinementCarrier
  factCarrier : RefinementCarrier
  mixedCarrier : RefinementCarrier


record LegalRefinementReceipt
  (oldGraph newGraph : Algebra.LegalGraph)
  (oldFacts newFacts : Algebra.FactSet)
  : Set where
  constructor legal-refinement-receipt
  field
    graphRefinement : GraphRefinement oldGraph newGraph
    factRefinement : FactRefinement oldFacts newFacts
    residualKind : Residual.LegalResidualKind
    acquisitionRoute : Residual.LegalAcquisitionRoute
    carrier : RefinementCarrier
    oldHistoryPreserved : Bool
    oldHistoryPreservedIsTrue : oldHistoryPreserved ≡ true
    conclusionsMustBeRecomputed : Bool
    conclusionsMustBeRecomputedIsTrue : conclusionsMustBeRecomputed ≡ true

open LegalRefinementReceipt public

------------------------------------------------------------------------
-- Re-run status is proposition-relative. The same refinement can open one goal,
-- close another via an exception/defeater, and leave a third unchanged.
------------------------------------------------------------------------

data RerunDisposition : Set where
  newlyReachable : RerunDisposition
  stillReachable : RerunDisposition
  newlyDefeated : RerunDisposition
  stillUnreachable : RerunDisposition
  unresolvedAfterRefinement : RerunDisposition


record LegalRerunResult
  (oldGraph newGraph : Algebra.LegalGraph)
  (oldFacts newFacts : Algebra.FactSet)
  (goal : Algebra.LegalProposition)
  : Set where
  constructor legal-rerun-result
  field
    disposition : RerunDisposition
    oldReachabilityEvidence : Set
    newReachabilityEvidence : Set
    changeExplanation : String
    sourceProvenanceRechecked : Set

open LegalRerunResult public

------------------------------------------------------------------------
-- Cut computation must also be re-run on the refined graph. We do not pretend
-- that a cut on G remains minimal on G'.
------------------------------------------------------------------------

record RefinedCutComputation
  (oldGraph newGraph : Algebra.LegalGraph)
  (oldFacts newFacts : Algebra.FactSet)
  (goal : Algebra.LegalProposition)
  : Set where
  constructor refined-cut-computation
  field
    oldCut : Algebra.MinimalCut oldGraph oldFacts goal
    newCut : Algebra.MinimalCut newGraph newFacts goal
    cutChanged : Bool
    cutChangeExplanation : String

open RefinedCutComputation public

------------------------------------------------------------------------
-- Selective reopening request: the residual tells us what to reacquire; the
-- refined graph then reruns only the issue/dependency fibre that consumes it.
------------------------------------------------------------------------

record LegalSelectiveReopenRequest : Set where
  constructor legal-selective-reopen-request
  field
    residual : Residual.LegalResidualKind
    acquisition : Residual.LegalAcquisitionRoute
    issueReference : String
    reopenUniversalGraph : Bool
    reopenIssueProjection : Bool
    reopenOperationalOutcome : Bool
    preserveUnaffectedHistory : Bool
    preserveUnaffectedHistoryIsTrue : preserveUnaffectedHistory ≡ true

open LegalSelectiveReopenRequest public

requestForResidual : Residual.LegalResidualKind → String → LegalSelectiveReopenRequest
requestForResidual Residual.missingRemedyExecution issue =
  legal-selective-reopen-request
    Residual.missingRemedyExecution Residual.inspectExecutionEvidence issue
    false false true true refl
requestForResidual Residual.missingCommunityOutcome issue =
  legal-selective-reopen-request
    Residual.missingCommunityOutcome Residual.inspectCommunityOutcomeEvidence issue
    false false true true refl
requestForResidual kind issue =
  legal-selective-reopen-request
    kind (Residual.preferredRoute kind) issue
    true true false true refl

------------------------------------------------------------------------
-- Non-monotone-law firewalls.
------------------------------------------------------------------------

data GraphExtensionPreservesEveryOldLegalConclusion : Set where
data NewFactCanOnlyOpenAndNeverDefeat : Set where
data OldMinimalCutRemainsMinimalAfterRefinement : Set where
data RecomputeMeansRewritePriorProvenance : Set where

graphExtensionIsNotConclusionMonotone :
  GraphExtensionPreservesEveryOldLegalConclusion → ⊥
graphExtensionIsNotConclusionMonotone ()

newFactsMayActivateExceptionsOrDefeaters : NewFactCanOnlyOpenAndNeverDefeat → ⊥
newFactsMayActivateExceptionsOrDefeaters ()

minimalCutMustBeRechecked : OldMinimalCutRemainsMinimalAfterRefinement → ⊥
minimalCutMustBeRechecked ()

rerunDoesNotRewriteHistory : RecomputeMeansRewritePriorProvenance → ⊥
rerunDoesNotRewriteHistory ()

appendOnlyCoreStillApplies :
  CoreReopen.NewResidualMayRewriteOldSourceProvenance → ⊥
appendOnlyCoreStillApplies = CoreReopen.newResidualDoesNotRewriteOldProvenance
