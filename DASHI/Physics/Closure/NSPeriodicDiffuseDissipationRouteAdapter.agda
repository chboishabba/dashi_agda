module DASHI.Physics.Closure.NSPeriodicDiffuseDissipationRouteAdapter where

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥; ⊥-elim)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicDiffuseDissipationCharging as Charge
import DASHI.Physics.Closure.NSPeriodicDiffuseSpectrumBKMCompletion as Diffuse
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact constructor selecting the dissipation-charging branch of the diffuse
-- spectrum completion theorem.
------------------------------------------------------------------------

record PeriodicDiffuseDissipationRouteInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (InitialDatum Solution Time State Shell : Set i) : Set (lsuc i) where
  field
    SolvesFrom : InitialDatum → Solution → Set i
    StateAt : Solution → Time → State

    ShellEnergy : Shell → State → Set i
    TotalEnergy : State → Set i
    MaxShellFractionBelowThreshold : State → Set i

    DiffuseAt : Solution → Time → Set i
    VorticityTimeIntegralFinite : Solution → Time → Set i

    diffuseCriterion : ∀ u T →
      DiffuseAt u T →
      MaxShellFractionBelowThreshold (StateAt u T)

    chargeInputs : ∀ u₀ u T →
      SolvesFrom u₀ u →
      DiffuseAt u T →
      Charge.PeriodicDiffuseDissipationChargeInputs A

    chargeFiniteMeansVorticityFinite :
      ∀ u₀ u T
        (solves : SolvesFrom u₀ u)
        (diffuse : DiffuseAt u T) →
      Charge.VorticityExpenditureFinite
        (chargeInputs u₀ u T solves diffuse) →
      VorticityTimeIntegralFinite u T

open PeriodicDiffuseDissipationRouteInputs public

diffuseDissipationRouteToBKMInputs :
  ∀ {i} {A : AbsorptionArithmetic}
    {InitialDatum Solution Time State Shell : Set i} →
  PeriodicDiffuseDissipationRouteInputs
    A InitialDatum Solution Time State Shell →
  Diffuse.PeriodicDiffuseSpectrumBKMInputs
    InitialDatum Solution Time State Shell
diffuseDissipationRouteToBKMInputs D = record
  { SolvesFrom = SolvesFrom D
  ; StateAt = StateAt D
  ; ShellEnergy = ShellEnergy D
  ; TotalEnergy = TotalEnergy D
  ; MaxShellFractionBelowThreshold = MaxShellFractionBelowThreshold D
  ; DiffuseAt = DiffuseAt D
  ; VorticityTimeIntegralFinite = VorticityTimeIntegralFinite D
  ; ShellSpreadControl = λ u T → ⊥
  ; SmallRegularityControl = λ u₀ u T → ⊥
  ; DissipationChargeControl = λ u T → VorticityTimeIntegralFinite D u T
  ; diffuseCriterion = diffuseCriterion D
  ; selectDiffuseControl = λ u₀ u T solves diffuse →
      Diffuse.dissipationChargeRoute
        (chargeFiniteMeansVorticityFinite D u₀ u T solves diffuse
          (Charge.diffuseDissipationChargeGivesFiniteVorticity
            (chargeInputs D u₀ u T solves diffuse)))
  ; shellSpreadGivesBKM = λ u T impossible → ⊥-elim impossible
  ; smallRegularityGivesBKM = λ u₀ u T solves impossible → ⊥-elim impossible
  ; dissipationChargeGivesBKM = λ u T finite → finite
  }

diffuseDissipationRouteGivesBKM :
  ∀ {i} {A : AbsorptionArithmetic}
    {InitialDatum Solution Time State Shell : Set i} →
  (D : PeriodicDiffuseDissipationRouteInputs
    A InitialDatum Solution Time State Shell) →
  ∀ u₀ u T →
  SolvesFrom D u₀ u →
  DiffuseAt D u T →
  VorticityTimeIntegralFinite D u T
diffuseDissipationRouteGivesBKM D =
  Diffuse.periodicDiffuseSpectrumGivesBKM
    (diffuseDissipationRouteToBKMInputs D)

------------------------------------------------------------------------
-- Status: the generic diffuse dispatcher is concretely inhabited by the
-- dissipation-charging theorem.  The remaining PDE leaf is chargeInputs.
------------------------------------------------------------------------

diffuseDissipationRouteAdapterLevel : ProofLevel
diffuseDissipationRouteAdapterLevel = machineChecked
