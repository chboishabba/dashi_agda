module DASHI.Physics.Motors.MadScience369V2PulsedCoenergyRecoveryBidiExact where

------------------------------------------------------------------------
-- Exact finite energy partitions and source identities for a
-- hypothetical pulse-controlled reluctance generator.
-- Original madscience369 V2 claims remain separate from the distinct
-- Donald Smith/Filsinger timed-pump and circuit 369/27 donors.
--
-- A Nat energy quantum is a finite selected numerical accounting grid,
-- not an observed power flow or a real differentiable co-energy model.
-- The nonlinear derivative identities are tested independently in SymPy,
-- and physical pulse timing / winding parameters are still OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Recover
import DASHI.Physics.Motors.Circuit36927SwitchStateExact as Switch

-- Pulse edges are structural state transitions. The switch model does not
-- contain diode recovery, switch energy, inductive flyback or a source coil.
conditionalToggleInvolution : (s : Switch.SwitchState) →
  Switch.nextState Switch.toggle (Switch.nextState Switch.toggle s) ≡ s
conditionalToggleInvolution = Switch.toggleIsInvolution

-- Same-window mechanical/source/controller/stored-energy partition.
-- The balance is supplied, NEVER inferred from a product or a video.
record V2PulsedEnergyWindow : Set where
  constructor v2PulsedEnergyWindow
  field
    mechanicalInput : Nat
    independentControllerInput : Nat
    initiallyStored : Nat
    loadOutput : Nat
    copperCoreHeat : Nat
    switchingLoss : Nat
    finallyStored : Nat
    closedOriginalBoundary :
      (mechanicalInput + independentControllerInput) + initiallyStored
      ≡ loadOutput + (copperCoreHeat + (switchingLoss + finallyStored))

allInputs : V2PulsedEnergyWindow → Nat
allInputs w =
  (V2PulsedEnergyWindow.mechanicalInput w
     + V2PulsedEnergyWindow.independentControllerInput w)
     + V2PulsedEnergyWindow.initiallyStored w

-- Nonnegative heat and switching dissipation prohibit an invented gain
-- when the supplied original boundary is complete.
pulsedLoadNotGreaterThanAllInputs : (w : V2PulsedEnergyWindow) →
  Recover._≤_ (V2PulsedEnergyWindow.loadOutput w) (allInputs w)
pulsedLoadNotGreaterThanAllInputs w =
  Recover.transportUpper
    (Recover.sym (V2PulsedEnergyWindow.closedOriginalBoundary w))
    (Recover.≤-append
      (V2PulsedEnergyWindow.loadOutput w)
      (V2PulsedEnergyWindow.copperCoreHeat w
        + (V2PulsedEnergyWindow.switchingLoss w
          + V2PulsedEnergyWindow.finallyStored w)))

-- A modelled energy-recovery improvement transfers some of the energy
-- formerly dissipated in a clamp to useful load output.  No such
-- transfer is asserted of V2 without source-selected switch measurements.
record RecoveryReroutingReceipt : Set where
  constructor recoveryReroutingReceipt
  field
    beforeUseful : Nat
    recoverableClampDump : Nat
    afterUseful : Nat
    accountingRerouting : afterUseful ≡ beforeUseful + recoverableClampDump

reroutingCannotDecreaseUseful : (r : RecoveryReroutingReceipt) →
  Recover._≤_ (RecoveryReroutingReceipt.beforeUseful r)
               (RecoveryReroutingReceipt.afterUseful r)
reroutingCannotDecreaseUseful r =
  Recover.transportUpper
    (Recover.sym (RecoveryReroutingReceipt.accountingRerouting r))
    (Recover.≤-append (RecoveryReroutingReceipt.beforeUseful r)
                      (RecoveryReroutingReceipt.recoverableClampDump r))

-- Numeric countermodel only: exactly the same 45 energy units of
-- mechanical input, different routing losses and useful electrical work.
-- No claim this matches the actual V2 45 W reported load.
uncorrectedPulseLedger : V2PulsedEnergyWindow
uncorrectedPulseLedger = v2PulsedEnergyWindow
  45 0 0 31 12 2 0 refl

recoveringPulseLedger : V2PulsedEnergyWindow
recoveringPulseLedger = v2PulsedEnergyWindow
  45 0 0 34 8 3 0 refl

-- Quantified model improvement, but not self-running or anomalous energy.
modelRerouting : RecoveryReroutingReceipt
modelRerouting = recoveryReroutingReceipt 31 3 34 refl

modelImprovement : Recover._≤_ 31 34
modelImprovement = reroutingCannotDecreaseUseful modelRerouting

-- The donor's separate independent-natural-source case is deliberately not
-- smuggled into the rotor ledger.  Same-object evidence must be provided.
record V2PhysicalAdmission : Set₁ where
  field
    SelectedOriginalV2Netlist : Set
    SameV2CoenergyFluxMap : Set
    ActualPulseSwitchingLoss : Set
    IndependentControllerWorkReceipt : Set
    SameWindowShaftTorqueAndTerminalWork : Set
    ActualStorageEndpointReceipt : Set
    netlist : SelectedOriginalV2Netlist
    flux : SameV2CoenergyFluxMap
    switching : ActualPulseSwitchingLoss
    modulator : IndependentControllerWorkReceipt
    timing : SameWindowShaftTorqueAndTerminalWork
    storage : ActualStorageEndpointReceipt