module DASHI.Physics.Plasma.ToroidalConstantMagnitudeAlfvenicFlowExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalConstantMagnitudeZeroBounceSeedExact as Seed
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

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
-- because grad(B^2)=0.  This pays magnetic tension by flow inertia without
-- modifying |B| and therefore without reintroducing magnetic-mirror bounce.
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
    false refl
    false refl
    true refl

alfvenicIdentityReference : String
alfvenicIdentityReference =
  "For div B = 0 and grad(B^2)=0: JxB=(B.grad)B/mu0. With u=+/-B/sqrt(mu0 rho), rho(u.grad)u=JxB and uxB=0."
