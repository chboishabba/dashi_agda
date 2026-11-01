module DASHI.Physics.Plasma.ElsasserMHDChartExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ELSASSER CHART
--
-- z+ = u + b_A, z- = u - b_A is represented as a reversible chart on the
-- same MHD state fibre.  The chart does not create new physics; it reorganises
-- the nonlinear interaction so each Elsasser field is advected by the other.
------------------------------------------------------------------------

record ElsasserChart : Set₁ where
  constructor elsasser-chart
  field
    Velocity MagneticAlfven Plus Minus : Set
    encodePlus : Velocity → MagneticAlfven → Plus
    encodeMinus : Velocity → MagneticAlfven → Minus
    recoverVelocity : Plus → Minus → Velocity
    recoverMagnetic : Plus → Minus → MagneticAlfven

    plusRoundTrip :
      (u : Velocity) (b : MagneticAlfven) →
      recoverVelocity (encodePlus u b) (encodeMinus u b) ≡ u

    magneticRoundTrip :
      (u : Velocity) (b : MagneticAlfven) →
      recoverMagnetic (encodePlus u b) (encodeMinus u b) ≡ b

    chartReference : String

open ElsasserChart public

record ElsasserDynamics (chart : ElsasserChart) : Set₁ where
  constructor elsasser-dynamics
  field
    State : Set
    Pressure : Set
    Dissipation : Set
    plusField : State → Plus chart
    minusField : State → Minus chart

    PlusAdvectedByMinus : Set
    MinusAdvectedByPlus : Set
    pressureCouplesBoth : Set
    dissipativeCoupling : Dissipation
    dynamicsReference : String

open ElsasserDynamics public

------------------------------------------------------------------------
-- Nonlinear-structure firewall.
------------------------------------------------------------------------

record ElsasserBoundary : Set where
  constructor elsasser-boundary
  field
    elsasserVariablesAreNewPhysicalDegreesOfFreedom : Bool
    elsasserVariablesAreNewPhysicalDegreesOfFreedomIsFalse :
      elsasserVariablesAreNewPhysicalDegreesOfFreedom ≡ false

    plusFieldSelfAdvectsByDefinition : Bool
    plusFieldSelfAdvectsByDefinitionIsFalse :
      plusFieldSelfAdvectsByDefinition ≡ false

    minusFieldSelfAdvectsByDefinition : Bool
    minusFieldSelfAdvectsByDefinitionIsFalse :
      minusFieldSelfAdvectsByDefinition ≡ false

    oppositeElsasserInteractionShapeIsOwned : Bool
    oppositeElsasserInteractionShapeIsOwnedIsTrue :
      oppositeElsasserInteractionShapeIsOwned ≡ true

    navierStokesSingleFieldNonlinearityEqualsMHDByDefinition : Bool
    navierStokesSingleFieldNonlinearityEqualsMHDByDefinitionIsFalse :
      navierStokesSingleFieldNonlinearityEqualsMHDByDefinition ≡ false

canonicalElsasserBoundary : ElsasserBoundary
canonicalElsasserBoundary =
  elsasser-boundary false refl false refl false refl true refl false refl
