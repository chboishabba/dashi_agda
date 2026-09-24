module DASHI.Physics.Foundations.ResonantFlightWingLoadRecoveryCompilerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ResonantFlightPhaseEnergyRoutingExact as Route
import DASHI.Physics.Foundations.ResonantFlightPowerSignExact as Sign

------------------------------------------------------------------------
-- Compiler from phase-resolved wing loading into regenerative routing.
------------------------------------------------------------------------

record WingLoadRecoveryCompiler : Set₁ where
  constructor wing-load-recovery-compiler
  field
    WingLoad Store Bus ReturnedWingLoad : Set
    capture : WingLoad → Store
    toBus : Store → Bus
    return : Bus → ReturnedWingLoad

open WingLoadRecoveryCompiler public

recoverThroughBus :
  (C : WingLoadRecoveryCompiler) →
  WingLoad C →
  ReturnedWingLoad C
recoverThroughBus C w =
  WingLoadRecoveryCompiler.return C
    (WingLoadRecoveryCompiler.toBus C
      (WingLoadRecoveryCompiler.capture C w))

record SignedWingLoadRecovery : Set₁ where
  constructor signed-wing-load-recovery
  field
    WingLoad Store : Set
    signOf : WingLoad → Sign.PowerSign
    recover : WingLoad → Store
    negative-load-is-recoverable :
      (w : WingLoad) →
      signOf w ≡ Sign.negative →
      Store

open SignedWingLoadRecovery public

negativeWingLoadHasRecoveryTarget :
  (R : SignedWingLoadRecovery) →
  (w : WingLoad R) →
  signOf R w ≡ Sign.negative →
  Store R
negativeWingLoadHasRecoveryTarget R w p =
  negative-load-is-recoverable R w p
