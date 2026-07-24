module DASHI.Physics.Closure.NSPeriodicDiffuseSpectrumBKMCompletion where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Scale-free diffuse-spectrum branch.
--
-- A diffuse state is not forced into a packet chart.  Instead an inhabitant must
-- supply one of three proof-relevant mechanisms: distributed shell
-- reconstruction, direct small/high-regularity control, or dissipation charging.
-- The selected mechanism is then converted to the common finite-vorticity
-- expenditure endpoint.
------------------------------------------------------------------------

data DiffuseControlRoute
    {s r d : Level}
    (ShellSpreadControl : Set s)
    (SmallRegularityControl : Set r)
    (DissipationChargeControl : Set d) : Set (s ⊔ r ⊔ d) where
  shellSpreadRoute :
    ShellSpreadControl →
    DiffuseControlRoute
      ShellSpreadControl SmallRegularityControl DissipationChargeControl
  smallRegularityRoute :
    SmallRegularityControl →
    DiffuseControlRoute
      ShellSpreadControl SmallRegularityControl DissipationChargeControl
  dissipationChargeRoute :
    DissipationChargeControl →
    DiffuseControlRoute
      ShellSpreadControl SmallRegularityControl DissipationChargeControl

record PeriodicDiffuseSpectrumBKMInputs
    {i : Level}
    (InitialDatum Solution Time State Shell : Set i) : Set (lsuc i) where
  field
    SolvesFrom : InitialDatum → Solution → Set i
    StateAt : Solution → Time → State

    ShellEnergy : Shell → State → Set i
    TotalEnergy : State → Set i
    MaxShellFractionBelowThreshold : State → Set i

    DiffuseAt : Solution → Time → Set i
    VorticityTimeIntegralFinite : Solution → Time → Set i

    ShellSpreadControl : Solution → Time → Set i
    SmallRegularityControl : InitialDatum → Solution → Time → Set i
    DissipationChargeControl : Solution → Time → Set i

    diffuseCriterion : ∀ u T →
      DiffuseAt u T →
      MaxShellFractionBelowThreshold (StateAt u T)

    selectDiffuseControl : ∀ u₀ u T →
      SolvesFrom u₀ u →
      DiffuseAt u T →
      DiffuseControlRoute
        (ShellSpreadControl u T)
        (SmallRegularityControl u₀ u T)
        (DissipationChargeControl u T)

    shellSpreadGivesBKM : ∀ u T →
      ShellSpreadControl u T →
      VorticityTimeIntegralFinite u T

    smallRegularityGivesBKM : ∀ u₀ u T →
      SolvesFrom u₀ u →
      SmallRegularityControl u₀ u T →
      VorticityTimeIntegralFinite u T

    dissipationChargeGivesBKM : ∀ u T →
      DissipationChargeControl u T →
      VorticityTimeIntegralFinite u T

open PeriodicDiffuseSpectrumBKMInputs public

periodicDiffuseSpectrumGivesBKM :
  ∀ {i} {InitialDatum Solution Time State Shell : Set i} →
  (D : PeriodicDiffuseSpectrumBKMInputs
    InitialDatum Solution Time State Shell) →
  ∀ u₀ u T →
  SolvesFrom D u₀ u →
  DiffuseAt D u T →
  VorticityTimeIntegralFinite D u T
periodicDiffuseSpectrumGivesBKM D u₀ u T solves diffuse
  with selectDiffuseControl D u₀ u T solves diffuse
... | shellSpreadRoute spread =
  shellSpreadGivesBKM D u T spread
... | smallRegularityRoute small =
  smallRegularityGivesBKM D u₀ u T solves small
... | dissipationChargeRoute charged =
  dissipationChargeGivesBKM D u T charged

------------------------------------------------------------------------
-- Proof-level and fail-closed status.
------------------------------------------------------------------------

diffuseRouteCaseAssemblyLevel : ProofLevel
diffuseRouteCaseAssemblyLevel = machineChecked

diffuseShellSpreadControlLevel : ProofLevel
diffuseShellSpreadControlLevel = conjectural

diffuseSmallRegularityControlLevel : ProofLevel
diffuseSmallRegularityControlLevel = conditional

diffuseDissipationChargeControlLevel : ProofLevel
diffuseDissipationChargeControlLevel = conjectural

diffuseSpectrumBKMInputsInhabited : Bool
diffuseSpectrumBKMInputsInhabited = false
