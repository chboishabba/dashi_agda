module DASHI.Foundations.Wette1969CertifiedTraceWeakeningExact where

------------------------------------------------------------------------
-- MONOTONE REPLAY / WEAKENING OF CERTIFIED WETTE HISTORICAL TRACES
--
-- Finite derivation contexts only grow by consing certified conclusions.  If
-- every formula available in C is also available in C', then every certified
-- historical rule selected at C can be re-selected at C'.  Recursing through a
-- trace yields a replayed trace together with a target-level preservation map.
--
-- This is the missing join operation for independently developed proof attempts:
-- two branches may begin at the same scaffold context; after executing one, the
-- other can be replayed over the enlarged context without changing its rule
-- bodies or premise proofs.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.Vec using (lookup)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

Context = Finite.DerivationContext
Formula = Signature.Formula
historicalSystem = Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem

PreservesContext : Context → Context → Set
PreservesContext before after =
  (formula : Formula) → formula Finite.∈Context before → formula Finite.∈Context after

identityPreservation : (context : Context) → PreservesContext context context
identityPreservation context formula evidence = evidence

extendPreservation :
  {before after : Context} →
  PreservesContext before after →
  (formula : Formula) →
  PreservesContext (formula ∷ before) (formula ∷ after)
extendPreservation preserve formula .formula Finite.here = Finite.here
extendPreservation preserve formula other (Finite.there evidence) =
  Finite.there (preserve other evidence)

weakenPremisesHold :
  {before after : Context} →
  (preserve : PreservesContext before after) →
  (rule : RuleBody.HistoricalRuleBody) →
  Historical.PremisesHold Finite.finiteHistoricalContextSystem before rule →
  Historical.PremisesHold Finite.finiteHistoricalContextSystem after rule
weakenPremisesHold preserve rule evidence index =
  preserve (lookup (RuleBody.premises rule) index) (evidence index)

weakenSelectedRule :
  {before after : Context} →
  (preserve : PreservesContext before after) →
  PCRA.SelectedRuleApplication historicalSystem before →
  PCRA.SelectedRuleApplication historicalSystem after
weakenSelectedRule {after = after} preserve selected =
  PCRA.selectedRuleApplication rule
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem after rule
      (weakenPremisesHold preserve rule
        (Dependency.precondition (PCRA.applicationProof selected))))
  where
    rule = PCRA.selectedRule selected

record WeakenedCertifiedTrace
    {before after : Context}
    (preserve : PreservesContext before after)
    (original : PCRA.CertifiedRuleTrace historicalSystem before) : Set₁ where
  constructor weakenedCertifiedTrace
  field
    replay : PCRA.CertifiedRuleTrace historicalSystem after
    targetPreservation :
      PreservesContext
        (PCRA.runCertifiedTrace historicalSystem original)
        (PCRA.runCertifiedTrace historicalSystem replay)

open WeakenedCertifiedTrace public

weakenCertifiedTrace :
  {before after : Context} →
  (preserve : PreservesContext before after) →
  (trace : PCRA.CertifiedRuleTrace historicalSystem before) →
  WeakenedCertifiedTrace preserve trace
weakenCertifiedTrace preserve PCRA.done =
  weakenedCertifiedTrace PCRA.done preserve
weakenCertifiedTrace preserve (PCRA.choose selected rest) =
  weakenedCertifiedTrace
    (PCRA.choose selected' (replay weakenedRest))
    (targetPreservation weakenedRest)
  where
    selected' = weakenSelectedRule preserve selected

    nextPreservation :
      PreservesContext
        (PCRA.applySelected historicalSystem selected)
        (PCRA.applySelected historicalSystem selected')
    nextPreservation =
      extendPreservation preserve (RuleBody.conclusion (PCRA.selectedRule selected))

    weakenedRest = weakenCertifiedTrace nextPreservation rest

weakenedTracePreservesProducedFormula :
  {before after : Context} →
  {formula : Formula} →
  (preserve : PreservesContext before after) →
  (trace : PCRA.CertifiedRuleTrace historicalSystem before) →
  formula Finite.∈Context (PCRA.runCertifiedTrace historicalSystem trace) →
  formula Finite.∈Context
    (PCRA.runCertifiedTrace historicalSystem
      (replay (weakenCertifiedTrace preserve trace)))
weakenedTracePreservesProducedFormula preserve trace evidence =
  targetPreservation (weakenCertifiedTrace preserve trace) _ evidence

record Wette1969CertifiedTraceWeakeningBoundary : Set where
  constructor wette1969CertifiedTraceWeakeningBoundary
  field
    selectedHistoricalRulesReplayUnderContextExtension : Bool
    selectedHistoricalRulesReplayUnderContextExtensionIsTrue :
      selectedHistoricalRulesReplayUnderContextExtension ≡ true
    entireCertifiedTracesReplayUnderContextExtension : Bool
    entireCertifiedTracesReplayUnderContextExtensionIsTrue :
      entireCertifiedTracesReplayUnderContextExtension ≡ true
    replayPreservesOriginalTargetFormulaAvailability : Bool
    replayPreservesOriginalTargetFormulaAvailabilityIsTrue :
      replayPreservesOriginalTargetFormulaAvailability ≡ true
    replayChangesHistoricalRuleBodies : Bool
    replayChangesHistoricalRuleBodiesIsFalse :
      replayChangesHistoricalRuleBodies ≡ false

canonicalWette1969CertifiedTraceWeakeningBoundary :
  Wette1969CertifiedTraceWeakeningBoundary
canonicalWette1969CertifiedTraceWeakeningBoundary =
  wette1969CertifiedTraceWeakeningBoundary
    true refl true refl true refl false refl
