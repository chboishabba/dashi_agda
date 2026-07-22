module DASHI.Physics.Closure.NSPeriodicFiveHalvesIntegratedRoute where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaDifferentialExpenditureProducer
open import DASHI.Physics.Closure.NSCompactGammaConcretePotentialInstantiation
open import DASHI.Physics.Closure.NSCompactGammaConcretePotentialCompletion

------------------------------------------------------------------------
-- Explicit time-integrated replacement for the falsified bare pointwise route.
--
-- No new analytic assumption is introduced: this module re-exports the existing
-- concrete potential/expenditure theorem at exactly the weighted-five-halves and
-- BKM endpoints needed by the corrected strategy.
------------------------------------------------------------------------

periodicIntegratedFiveHalvesBound :
  ∀ {t l : Level} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time)
    (I : ConcreteCompactGammaIntegration A P)
    (D : ConcretePotentialClosureData {l = l} A L C P I) →
  _≤_ A
    (weightedShellExpenditure D)
    (_+_ A
      (totalPotential P (initialTime P))
      (forcingAndDataRemainder I))
periodicIntegratedFiveHalvesBound =
  concrete-potential-finite-weighted-shell-expenditure

periodicIntegratedVorticityBound :
  ∀ {t l : Level} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time)
    (I : ConcreteCompactGammaIntegration A P)
    (D : ConcretePotentialClosureData {l = l} A L C P I) →
  _≤_ A
    (vorticityExpenditure D)
    (_+_ A
      (totalPotential P (initialTime P))
      (forcingAndDataRemainder I))
periodicIntegratedVorticityBound =
  concrete-potential-finite-vorticity-expenditure

periodicIntegratedRouteInvokesBKM :
  ∀ {t l : Level} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time)
    (I : ConcreteCompactGammaIntegration A P)
    (D : ConcretePotentialClosureData {l = l} A L C P I) →
  Continuation D
periodicIntegratedRouteInvokesBKM = concrete-potential-bkm-continuation

staticThresholdAdjacentRouteRejectedByFiniteWitness : Bool
staticThresholdAdjacentRouteRejectedByFiniteWitness = true

integratedRouteAssemblyMachineChecked : Bool
integratedRouteAssemblyMachineChecked = true

integratedRouteConcretePDELeavesInhabited : Bool
integratedRouteConcretePDELeavesInhabited = false

integratedRouteProvesUnconditionalGlobalRegularity : Bool
integratedRouteProvesUnconditionalGlobalRegularity = false
