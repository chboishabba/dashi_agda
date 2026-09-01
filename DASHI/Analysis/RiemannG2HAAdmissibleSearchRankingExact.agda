module DASHI.Analysis.RiemannG2HAAdmissibleSearchRankingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Analysis.RiemannG2HAConsumerQuotientActiveSearchExact as HA

------------------------------------------------------------------------
-- H_A SEARCH RANKING ONLY AFTER HARD GATES
--
-- Merged #647 proves that MDL/Pareto ranking is subordinate to two hard gates:
-- admissibility and consumer adequacy.  The current H_A branch already owns a
-- dependency-aware next-probe consumer.  This owner composes those two facts:
-- a cheap search move cannot win merely because it is cheap if it rebuilds
-- generic transform theory, imports a wrong carrier, or fails to target the
-- actual next missing H_A receipt.
------------------------------------------------------------------------

data SearchMove : Set where
  rebuildGenericTransformTheory
  reuseFiniteCharacterAsAnalyticHA
  runHAProbe : HA.HARecoveryProbe → SearchMove

SearchModel : Set
SearchModel = HA.HARecoveryState × SearchMove

MoveAdmissible : SearchModel → Set
MoveAdmissible (state , rebuildGenericTransformTheory) = ⊥
MoveAdmissible (state , reuseFiniteCharacterAsAnalyticHA) = ⊥
MoveAdmissible (state , runHAProbe probe) = ⊤

ProbeMatchesNext :
  (state : HA.HARecoveryState) →
  HA.HARecoveryProbe → Set
ProbeMatchesNext
  (HA.ha-recovery-state HA.missing action admissible hx formulaShift weilShift provenance)
  HA.recoverImplementationIdentity = ⊤
ProbeMatchesNext
  (HA.ha-recovery-state HA.owned HA.missing admissible hx formulaShift weilShift provenance)
  HA.recoverParameterizedAction = ⊤
ProbeMatchesNext
  (HA.ha-recovery-state HA.owned HA.owned HA.missing hx formulaShift weilShift provenance)
  HA.recoverAdmissibility = ⊤
ProbeMatchesNext
  (HA.ha-recovery-state HA.owned HA.owned HA.owned HA.missing formulaShift weilShift provenance)
  HA.recoverCanonicalHXAgreement = ⊤
ProbeMatchesNext
  (HA.ha-recovery-state HA.owned HA.owned HA.owned HA.owned HA.missing weilShift provenance)
  HA.recoverSameFormulaSpectralShift = ⊤
ProbeMatchesNext
  (HA.ha-recovery-state HA.owned HA.owned HA.owned HA.owned HA.owned HA.missing provenance)
  HA.recoverSameWeilTransformShift = ⊤
ProbeMatchesNext
  (HA.ha-recovery-state HA.owned HA.owned HA.owned HA.owned HA.owned HA.owned HA.anonymous)
  HA.recoverSourceProvenance = ⊤
ProbeMatchesNext
  (HA.ha-recovery-state HA.owned HA.owned HA.owned HA.owned HA.owned HA.owned HA.sourceNative)
  HA.compileProofRelevantHA = ⊤
ProbeMatchesNext state probe = ⊥

MoveConsumerAdequate : SearchModel → Set
MoveConsumerAdequate (state , rebuildGenericTransformTheory) = ⊥
MoveConsumerAdequate (state , reuseFiniteCharacterAsAnalyticHA) = ⊥
MoveConsumerAdequate (state , runHAProbe probe) = ProbeMatchesNext state probe

moveDescriptionLength : SearchModel → Nat
moveDescriptionLength (state , rebuildGenericTransformTheory) = zero
moveDescriptionLength (state , reuseFiniteCharacterAsAnalyticHA) = zero
moveDescriptionLength (state , runHAProbe probe) = suc zero

haSearchMDLProblem : MDL.ConsumerMDLProblem
haSearchMDLProblem =
  MDL.consumerMDLProblem
    SearchModel
    MoveAdmissible
    MoveConsumerAdequate
    moveDescriptionLength
    (λ left right → ⊤)
    modelReference
    "H_A recovery search cost is ranked only after same-carrier and consumer-target gates"
    "Riemann G2 proof-relevant canonical H_A next-receipt consumer"
  where
    modelReference : SearchModel → String
    modelReference (state , rebuildGenericTransformTheory) =
      "rebuild generic transform theory (inadmissible)"
    modelReference (state , reuseFiniteCharacterAsAnalyticHA) =
      "reuse finite character carrier as analytic H_A (inadmissible)"
    modelReference (state , runHAProbe probe) =
      "run state-selected H_A recovery probe"

allMissingState : HA.HARecoveryState
allMissingState =
  HA.ha-recovery-state
    HA.missing HA.missing HA.missing HA.missing HA.missing HA.missing HA.anonymous

implementationProbeEligible :
  MDL.Eligible haSearchMDLProblem
    (allMissingState , runHAProbe HA.recoverImplementationIdentity)
implementationProbeEligible = tt , tt

wrongLaterProbeNotAdequate :
  MoveConsumerAdequate
    (allMissingState , runHAProbe HA.recoverSameFormulaSpectralShift) → ⊥
wrongLaterProbeNotAdequate x = x

cheapGenericMoveNotEligible :
  MDL.Eligible haSearchMDLProblem
    (allMissingState , rebuildGenericTransformTheory) → ⊥
cheapGenericMoveNotEligible eligible = proj₁ eligible

cheapFiniteCharacterMoveNotEligible :
  MDL.Eligible haSearchMDLProblem
    (allMissingState , reuseFiniteCharacterAsAnalyticHA) → ⊥
cheapFiniteCharacterMoveNotEligible eligible = proj₁ eligible

wrongLaterProbeNotEligible :
  MDL.Eligible haSearchMDLProblem
    (allMissingState , runHAProbe HA.recoverSameFormulaSpectralShift) → ⊥
wrongLaterProbeNotEligible eligible = proj₂ eligible

paretoSelectionCarriesHardGates :
  (costs : MDL.CostHyperfabric haSearchMDLProblem) →
  (selected : SearchModel) →
  MDL.ParetoAdmissible costs selected →
  MDL.Eligible haSearchMDLProblem selected
paretoSelectionCarriesHardGates costs selected receipt =
  MDL.selectedEligible receipt

cheapGenericMoveCannotBeParetoSelected :
  (costs : MDL.CostHyperfabric haSearchMDLProblem) →
  MDL.ParetoAdmissible costs
    (allMissingState , rebuildGenericTransformTheory) → ⊥
cheapGenericMoveCannotBeParetoSelected costs receipt =
  cheapGenericMoveNotEligible
    (paretoSelectionCarriesHardGates
      costs
      (allMissingState , rebuildGenericTransformTheory)
      receipt)

cheapFiniteCharacterCannotBeParetoSelected :
  (costs : MDL.CostHyperfabric haSearchMDLProblem) →
  MDL.ParetoAdmissible costs
    (allMissingState , reuseFiniteCharacterAsAnalyticHA) → ⊥
cheapFiniteCharacterCannotBeParetoSelected costs receipt =
  cheapFiniteCharacterMoveNotEligible
    (paretoSelectionCarriesHardGates
      costs
      (allMissingState , reuseFiniteCharacterAsAnalyticHA)
      receipt)

wrongLaterProbeCannotBeParetoSelected :
  (costs : MDL.CostHyperfabric haSearchMDLProblem) →
  MDL.ParetoAdmissible costs
    (allMissingState , runHAProbe HA.recoverSameFormulaSpectralShift) → ⊥
wrongLaterProbeCannotBeParetoSelected costs receipt =
  wrongLaterProbeNotEligible
    (paretoSelectionCarriesHardGates
      costs
      (allMissingState , runHAProbe HA.recoverSameFormulaSpectralShift)
      receipt)

record HAAdmissibleSearchRankingBoundary : Set where
  constructor ha-admissible-search-ranking-boundary
  field
    costRankingMayPrecedeCarrierAndConsumerGates : Bool
    costRankingMayPrecedeCarrierAndConsumerGatesIsFalse :
      costRankingMayPrecedeCarrierAndConsumerGates ≡ false

    genericTransformRebuildCanWinBecauseItIsCheap : Bool
    genericTransformRebuildCanWinBecauseItIsCheapIsFalse :
      genericTransformRebuildCanWinBecauseItIsCheap ≡ false

    wrongCarrierFiniteCharacterCanWinBecauseItIsCheap : Bool
    wrongCarrierFiniteCharacterCanWinBecauseItIsCheapIsFalse :
      wrongCarrierFiniteCharacterCanWinBecauseItIsCheap ≡ false

    laterReceiptMaySkipCurrentMissingDependencyBecauseItIsCheap : Bool
    laterReceiptMaySkipCurrentMissingDependencyBecauseItIsCheapIsFalse :
      laterReceiptMaySkipCurrentMissingDependencyBecauseItIsCheap ≡ false

    admissibilityThenConsumerAdequacyThenRanking : Bool
    admissibilityThenConsumerAdequacyThenRankingIsTrue :
      admissibilityThenConsumerAdequacyThenRanking ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHAAdmissibleSearchRankingBoundary :
  HAAdmissibleSearchRankingBoundary
canonicalHAAdmissibleSearchRankingBoundary =
  ha-admissible-search-ranking-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl
    "Cross-pollinate the merged admissible-MDL/Pareto theorem into H_A search literally: first require a semantically admissible search move, then require that it targets the exact next missing consumer receipt, and only then rank eligible moves by cost or Pareto coordinates. A numerically cheap generic transform rebuild, wrong-carrier finite character action, or later-stage receipt cannot bypass these hard gates. At the all-missing state the implementation-identity probe is eligible while later shift probes are not. This is proof-search governance only; it does not inhabit the missing H_A source receipts and does not derive RH."
