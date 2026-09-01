module DASHI.Analysis.RiemannG2HAAdmissibleSearchRankingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Analysis.RiemannG2HAConsumerQuotientActiveSearchExact as HA
import DASHI.Analysis.RiemannG2HARecoveryDependencyFrontierExact as Frontier

------------------------------------------------------------------------
-- H_A SEARCH RANKING ONLY AFTER HARD GATES
--
-- Cross-pollination correction: ranking uses the actual dependency FRONTIER,
-- not the earlier serial first-missing policy.  Several mathematically
-- independent recovery probes may therefore be eligible simultaneously.
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

MoveConsumerAdequate : SearchModel → Set
MoveConsumerAdequate (state , rebuildGenericTransformTheory) = ⊥
MoveConsumerAdequate (state , reuseFiniteCharacterAsAnalyticHA) = ⊥
MoveConsumerAdequate (state , runHAProbe probe) = Frontier.ProbeEnabled state probe

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
    "H_A recovery search cost is ranked only after same-carrier and dependency-frontier gates"
    "Riemann G2 proof-relevant canonical H_A live recovery frontier"
  where
    modelReference : SearchModel → String
    modelReference (state , rebuildGenericTransformTheory) =
      "rebuild generic transform theory (inadmissible)"
    modelReference (state , reuseFiniteCharacterAsAnalyticHA) =
      "reuse finite character carrier as analytic H_A (inadmissible)"
    modelReference (state , runHAProbe probe) =
      "run enabled H_A recovery-frontier probe"

allMissingState : HA.HARecoveryState
allMissingState = Frontier.allMissingState

implementationProbeEligible :
  MDL.Eligible haSearchMDLProblem
    (allMissingState , runHAProbe HA.recoverImplementationIdentity)
implementationProbeEligible = tt , Frontier.implementationIdentityLive

actionProbeAlsoEligibleAtStart :
  MDL.Eligible haSearchMDLProblem
    (allMissingState , runHAProbe HA.recoverParameterizedAction)
actionProbeAlsoEligibleAtStart = tt , Frontier.parameterizedActionLive

provenanceProbeAlsoEligibleAtStart :
  MDL.Eligible haSearchMDLProblem
    (allMissingState , runHAProbe HA.recoverSourceProvenance)
provenanceProbeAlsoEligibleAtStart = tt , Frontier.sourceProvenanceLive

wrongLaterProbeNotAdequate :
  MoveConsumerAdequate
    (allMissingState , runHAProbe HA.recoverSameFormulaSpectralShift) → ⊥
wrongLaterProbeNotAdequate ()

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
wrongLaterProbeNotEligible eligible = wrongLaterProbeNotAdequate (proj₂ eligible)

paretoSelectionCarriesHardGates :
  (costs : MDL.CostHyperfabric haSearchMDLProblem) →
  (selected : SearchModel) →
  MDL.ParetoAdmissible costs selected →
  MDL.Eligible haSearchMDLProblem selected
paretoSelectionCarriesHardGates costs selected receipt = MDL.selectedEligible receipt

cheapGenericMoveCannotBeParetoSelected :
  (costs : MDL.CostHyperfabric haSearchMDLProblem) →
  MDL.ParetoAdmissible costs
    (allMissingState , rebuildGenericTransformTheory) → ⊥
cheapGenericMoveCannotBeParetoSelected costs receipt =
  cheapGenericMoveNotEligible
    (paretoSelectionCarriesHardGates
      costs (allMissingState , rebuildGenericTransformTheory) receipt)

cheapFiniteCharacterCannotBeParetoSelected :
  (costs : MDL.CostHyperfabric haSearchMDLProblem) →
  MDL.ParetoAdmissible costs
    (allMissingState , reuseFiniteCharacterAsAnalyticHA) → ⊥
cheapFiniteCharacterCannotBeParetoSelected costs receipt =
  cheapFiniteCharacterMoveNotEligible
    (paretoSelectionCarriesHardGates
      costs (allMissingState , reuseFiniteCharacterAsAnalyticHA) receipt)

wrongLaterProbeCannotBeParetoSelected :
  (costs : MDL.CostHyperfabric haSearchMDLProblem) →
  MDL.ParetoAdmissible costs
    (allMissingState , runHAProbe HA.recoverSameFormulaSpectralShift) → ⊥
wrongLaterProbeCannotBeParetoSelected costs receipt =
  wrongLaterProbeNotEligible
    (paretoSelectionCarriesHardGates
      costs (allMissingState , runHAProbe HA.recoverSameFormulaSpectralShift) receipt)

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

    serialFirstMissingPolicyRequiredForRanking : Bool
    serialFirstMissingPolicyRequiredForRankingIsFalse :
      serialFirstMissingPolicyRequiredForRanking ≡ false

    independentEnabledProbesMayCompeteInsideEligibleStratum : Bool
    independentEnabledProbesMayCompeteInsideEligibleStratumIsTrue :
      independentEnabledProbesMayCompeteInsideEligibleStratum ≡ true

    disabledLaterReceiptMayWinByCheapCost : Bool
    disabledLaterReceiptMayWinByCheapCostIsFalse :
      disabledLaterReceiptMayWinByCheapCost ≡ false

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
    false refl
    "Use the actual H_A dependency frontier as the consumer-adequacy gate, then rank only inside that eligible stratum. At the all-missing state implementation identity, source action, and source provenance are independent eligible probes, while formula/transform consequences remain disabled until the transported action exists. Cheap generic-transform rebuilding and wrong-carrier finite-character reuse remain inadmissible. Pareto/MDL cost may choose among simultaneously enabled probes but cannot activate a disabled dependency edge or create theorem authority. RH is not derived."
