module DASHI.Physics.Plasma.ToroidalConstantMagnitudeAlfvenicFlowExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalConstantMagnitudeZeroBounceSeedExact as Seed
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce
import DASHI.Physics.Plasma.ElsasserMHDChartExact as Elsasser
import DASHI.Physics.Plasma.ElsasserCounterpropagatingInteractionBidiExact as Counter

------------------------------------------------------------------------
-- ROUTE A: ALFVENIC-FLOW FORCE BALANCE
--
-- For a divergence-free constant-|B| field with constant density rho, choose
--
--   u = +/- B / sqrt(mu0 rho).
--
-- Then u x B = 0, so ideal induction remains stationary, while
--
--   rho (u . grad) u = (B . grad) B / mu0 = J x B
--
-- because grad(B^2)=0.  In Elsasser variables b_A=B/sqrt(mu0 rho), u=+/-b_A
-- sets one of z+/- to zero, placing the state on the repo's literal pure-
-- Elsasser nonlinear-depletion boundary.  This does not by itself prove
-- stability, dissipation control, or reactor realizability.
------------------------------------------------------------------------

record AlfvenicFlowBalanceReceipt
    (population : ZeroBounce.DeclaredParticlePopulation)
    (seed : Seed.ToroidalConstantMagnitudeSeed population) : Set₁ where
  constructor alfvenic-flow-balance-receipt
  field
    constantMassDensityReceipt : Set
    velocityParallelOrAntiparallelToBReceipt : Set
    alfvenicMagnitudeReceipt : Set
    idealInductionStationaryReceipt : Set
    convectiveInertiaEqualsMagneticTensionReceipt : Set
    pressureGradientResidualReceipt : Set
    incompressibilityOrContinuityReceipt : Set

    elsasserChartReceipt : Set
    oneElsasserFieldVanishesReceipt : Set
    pureElsasserNonlinearDepletionReceipt : Set

    zeroBouncePreservedReceipt : Set
    flowShearStabilityReceipt : Set
    alfvenMachOneBoundaryReceipt : Set
    sameFieldSamePopulationReceipt : Set
    receiptReference : String

open AlfvenicFlowBalanceReceipt public

record AlfvenicFlowBoundary : Set where
  constructor alfvenic-flow-boundary
  field
    constantMagnitudeMakesMagneticTensionIdentityAvailable : Bool
    constantMagnitudeMakesMagneticTensionIdentityAvailableIsTrue :
      constantMagnitudeMakesMagneticTensionIdentityAvailable ≡ true

    alfvenicStateMapsToPureElsasserBoundary : Bool
    alfvenicStateMapsToPureElsasserBoundaryIsTrue :
      alfvenicStateMapsToPureElsasserBoundary ≡ true

    pureElsasserDepletionAutomaticallyProvesGlobalStability : Bool
    pureElsasserDepletionAutomaticallyProvesGlobalStabilityIsFalse :
      pureElsasserDepletionAutomaticallyProvesGlobalStability ≡ false

    alfvenicFlowAutomaticallyStable : Bool
    alfvenicFlowAutomaticallyStableIsFalse :
      alfvenicFlowAutomaticallyStable ≡ false

    exactIdealMHDIdentityProvesReactorRealizability : Bool
    exactIdealMHDIdentityProvesReactorRealizabilityIsFalse :
      exactIdealMHDIdentityProvesReactorRealizability ≡ false

    zeroBounceMustRemainSameObject : Bool
    zeroBounceMustRemainSameObjectIsTrue :
      zeroBounceMustRemainSameObject ≡ true

canonicalAlfvenicFlowBoundary : AlfvenicFlowBoundary
canonicalAlfvenicFlowBoundary =
  alfvenic-flow-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl

alfvenicIdentityReference : String
alfvenicIdentityReference =
  "For div B = 0 and grad(B^2)=0: JxB=(B.grad)B/mu0. With u=+/-B/sqrt(mu0 rho), rho(u.grad)u=JxB and uxB=0; equivalently one Elsasser field vanishes."

elsasserDonorReference : String
elsasserDonorReference =
  "ElsasserMHDChartExact + ElsasserCounterpropagatingInteractionBidiExact: pure one-direction Elsasser state is an ideal nonlinear-depletion boundary."
