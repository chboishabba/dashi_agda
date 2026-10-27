module DASHI.Unified.TOE369MaxCutKernelBidiTernaryValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.TOE369MaxCutKernelBidiTernaryExact as Owner
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

toeFullGradeDimensionFirewallMatches :
  Owner.FullGrade.LinearDimensionCreatesFaithfulness → ⊥
toeFullGradeDimensionFirewallMatches =
  TOE.toe369FullGradeDimensionDoesNotCreateFaithfulness

unifierFullGradeDimensionFirewallMatches :
  Owner.FullGrade.LinearDimensionCreatesFaithfulness → ⊥
unifierFullGradeDimensionFirewallMatches =
  Unifier.unifier369FullGradeDimensionDoesNotCreateFaithfulness

toeProjectedDimensionFirewallMatches :
  Owner.Projected.DirectSumDimensionCreatesProjectedAction → ⊥
toeProjectedDimensionFirewallMatches =
  TOE.toe369ProjectedDimensionDoesNotCreateAction

unifierProjectedDimensionFirewallMatches :
  Owner.Projected.DirectSumDimensionCreatesProjectedAction → ⊥
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
  Owner.Ibrahim.FiniteChartCreatesLinearMultiplicityAction → ⊥
toeFiniteChartFirewallMatches =
  TOE.toe369FiniteChartDoesNotCreateLinearMultiplicityAction

unifierFiniteChartFirewallMatches :
  Owner.Ibrahim.FiniteChartCreatesLinearMultiplicityAction → ⊥
unifierFiniteChartFirewallMatches =
  Unifier.unifier369FiniteChartDoesNotCreateLinearMultiplicityAction
