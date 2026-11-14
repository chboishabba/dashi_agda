module DASHI.Physics.GR.SchutzholdInteractionWorkNormalizationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange
import DASHI.Physics.GR.SchutzholdEMGWSourceLawExact as Source

------------------------------------------------------------------------
-- SCHUTZHOLD EQ. (5) -> CONTROLLED-EXCHANGE WORK NORMALIZATION
--
-- The source already fixes the symbolic work/energy-transfer law:
--   d<E>/dt = hdot integral <(dy Az)^2 - (dx Az)^2> d^3r.
-- Therefore the remaining max-cut must not call the work law itself missing.
-- What remains experiment/field-theory specific is the numerical value of the
-- renormalised expectation/integral and its same-object realization in the
-- interaction carrier.
------------------------------------------------------------------------

data WorkNormalizationEquation : Set where
  sourceEnergyTransferRateEquation : WorkNormalizationEquation
  integratedInteractionWorkEquation : WorkNormalizationEquation

workNormalizationEquationText : WorkNormalizationEquation → String
workNormalizationEquationText sourceEnergyTransferRateEquation =
  Source.sourceEquationText Source.energyTransferEquation
workNormalizationEquationText integratedInteractionWorkEquation =
  "Delta E_EM = integral dt hdot integral d^3r <(dy Az)^2 - (dx Az)^2>"

record SchutzholdInteractionWorkLaw
    (interaction : Exchange.EMGWInteractionCarrier) : Set₁ where
  constructor schutzhold-interaction-work-law
  field
    GWAmplitudeDerivative : Set
    gwAmplitudeDerivative : GWAmplitudeDerivative

    RenormalizedDirectionalFieldExpectation : Set
    renormalizedDirectionalFieldExpectation :
      RenormalizedDirectionalFieldExpectation

    EnergyTransferRate : Set
    energyTransferRate : EnergyTransferRate

    sourceRateEquation : WorkNormalizationEquation
    sourceRateEquationIsEq5 :
      sourceRateEquation ≡ sourceEnergyTransferRateEquation

    interactionWork : Exchange.InteractionWork interaction

    Eq5RateRealizationReceipt : Set
    eq5RateRealizationReceipt : Eq5RateRealizationReceipt

    TimeIntegrationReceipt : Set
    timeIntegrationReceipt : TimeIntegrationReceipt

    SameInteractionWorkReceipt : Set
    sameInteractionWorkReceipt : SameInteractionWorkReceipt

open SchutzholdInteractionWorkLaw public

record SchutzholdWorkNormalizationBoundary : Set where
  constructor schutzhold-work-normalization-boundary
  field
    sourceEnergyTransferFormulaAlreadySpecified : Bool
    integratedWorkFormulaAlreadySpecified : Bool
    signRoutingAlreadySpecified : Bool
    newIndependentWorkLawNeeded : Bool
    renormalizedExpectationValueStillPhysical : Bool
    spacetimeIntegralCalibrationStillPhysical : Bool
    sameObjectInteractionWorkWeldStillRequired : Bool

canonicalSchutzholdWorkNormalizationBoundary :
  SchutzholdWorkNormalizationBoundary
canonicalSchutzholdWorkNormalizationBoundary =
  schutzhold-work-normalization-boundary
    true true true false true true true
