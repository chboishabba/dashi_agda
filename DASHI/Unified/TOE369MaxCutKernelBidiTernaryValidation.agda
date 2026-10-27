module DASHI.Unified.TOE369MaxCutKernelBidiTernaryValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.TOE369MaxCutKernelBidiTernaryExact as Owner
import DASHI.Reasoning.Trialectic369Selected3BFullGradeActionMaxCutExact as FullGrade
import DASHI.Reasoning.Trialectic369Selected3BProjectedActionMaxCutExact as Projected
import DASHI.Wikimedia.IbrahimMonster3BLinearShortestFrontierCorrectionExact as Ibrahim
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier

toeFullCubeNonPromotionMatches :
  Owner.FullCubeRotationFree → ⊥
toeFullCubeNonPromotionMatches =
  TOE.toe369FullCubeRotationNotFree

unifierFullCubeNonPromotionMatches :
  Owner.FullCubeRotationFree → ⊥
unifierFullCubeNonPromotionMatches =
  Unifier.unifier369FullCubeRotationNotFree

toeMonsterRepresentationNonPromotionMatches :
  TOE.toe369Ternary27MonsterRepresentationNotPromoted
  ≡ Owner.toe27MonsterRepresentationNotPromoted
toeMonsterRepresentationNonPromotionMatches = refl

unifierMonsterRepresentationNonPromotionMatches :
  Unifier.unifier369Ternary27MonsterRepresentationNotPromoted
  ≡ Owner.toe27MonsterRepresentationNotPromoted
unifierMonsterRepresentationNonPromotionMatches = refl

toeMonsterEmbeddingNonPromotionMatches :
  TOE.toe369Ternary27MonsterEmbeddingNotPromoted
  ≡ Owner.toe27MonsterEmbeddingNotPromoted
toeMonsterEmbeddingNonPromotionMatches = refl

unifierMonsterEmbeddingNonPromotionMatches :
  Unifier.unifier369Ternary27MonsterEmbeddingNotPromoted
  ≡ Owner.toe27MonsterEmbeddingNotPromoted
unifierMonsterEmbeddingNonPromotionMatches = refl

toeFullGradeDimensionFirewallMatches :
  FullGrade.LinearDimensionCreatesFaithfulness → ⊥
toeFullGradeDimensionFirewallMatches =
  TOE.toe369FullGradeDimensionDoesNotCreateFaithfulness

unifierFullGradeDimensionFirewallMatches :
  FullGrade.LinearDimensionCreatesFaithfulness → ⊥
unifierFullGradeDimensionFirewallMatches =
  Unifier.unifier369FullGradeDimensionDoesNotCreateFaithfulness

toeProjectedDimensionFirewallMatches :
  Projected.DirectSumDimensionCreatesProjectedAction → ⊥
toeProjectedDimensionFirewallMatches =
  TOE.toe369ProjectedDimensionDoesNotCreateAction

unifierProjectedDimensionFirewallMatches :
  Projected.DirectSumDimensionCreatesProjectedAction → ⊥
unifierProjectedDimensionFirewallMatches =
  Unifier.unifier369ProjectedDimensionDoesNotCreateAction

toeKernelTraceFirewallMatches :
  TOE.toe369KernelTrace53DoesNotIdentify3B
  ≡ Owner.toeKernelTrace53DoesNotIdentify3B
toeKernelTraceFirewallMatches = refl

unifierKernelTraceFirewallMatches :
  Unifier.unifier369KernelTrace53DoesNotIdentify3B
  ≡ Owner.toeKernelTrace53DoesNotIdentify3B
unifierKernelTraceFirewallMatches = refl

toeTernaryPhaseReductionFirewallMatches :
  TOE.toe369Ternary27PhaseReductionNotGlobalInversion
  ≡ Owner.toe27PhaseReductionNotGlobalInversion
toeTernaryPhaseReductionFirewallMatches = refl

unifierTernaryPhaseReductionFirewallMatches :
  Unifier.unifier369Ternary27PhaseReductionNotGlobalInversion
  ≡ Owner.toe27PhaseReductionNotGlobalInversion
unifierTernaryPhaseReductionFirewallMatches = refl

toeFiniteChartFirewallMatches :
  Ibrahim.FiniteChartCreatesLinearMultiplicityAction → ⊥
toeFiniteChartFirewallMatches =
  TOE.toe369FiniteChartDoesNotCreateLinearMultiplicityAction

unifierFiniteChartFirewallMatches :
  Ibrahim.FiniteChartCreatesLinearMultiplicityAction → ⊥
unifierFiniteChartFirewallMatches =
  Unifier.unifier369FiniteChartDoesNotCreateLinearMultiplicityAction

------------------------------------------------------------------------
-- Exact finite-27 codec BIDI and compiled-host non-promotion regression.
------------------------------------------------------------------------

ownerStateDecodeStateCode :
  (e : Owner.TernaryEncodedState) →
  Owner.toe27StateDecode (Owner.toe27StateCode e) ≡ e
ownerStateDecodeStateCode =
  Owner.toe27StateDecodeStateCode

ownerStateCodeStateDecode :
  (i : Owner.TernaryState27) →
  Owner.toe27StateCode (Owner.toe27StateDecode i) ≡ i
ownerStateCodeStateDecode =
  Owner.toe27StateCodeStateDecode

toeStateCodeStateDecode :
  (i : Owner.TernaryState27) →
  TOE.toe369Ternary27StateCode (TOE.toe369Ternary27StateDecode i) ≡ i
toeStateCodeStateDecode =
  TOE.toe369Ternary27StateCodeStateDecode

unifierStateCodeStateDecode :
  (i : Owner.TernaryState27) →
  Unifier.unifier369Ternary27StateCode
    (Unifier.unifier369Ternary27StateDecode i) ≡ i
unifierStateCodeStateDecode =
  Unifier.unifier369Ternary27StateCodeStateDecode

toeRuntimeSourceStillDoesNotCreateKernelCertification =
  TOE.toe369Ternary27RuntimeSourceDoesNotCreateKernelCertification

unifierRuntimeSourceStillDoesNotCreateKernelCertification =
  Unifier.unifier369Ternary27RuntimeSourceDoesNotCreateKernelCertification

toeCompilerSuccessStillDoesNotCreateAgdaKernelSuccess =
  TOE.toe369Ternary27CompilerSuccessDoesNotCreateAgdaKernelSuccess

unifierCompilerSuccessStillDoesNotCreateAgdaKernelSuccess =
  Unifier.unifier369Ternary27CompilerSuccessDoesNotCreateAgdaKernelSuccess
