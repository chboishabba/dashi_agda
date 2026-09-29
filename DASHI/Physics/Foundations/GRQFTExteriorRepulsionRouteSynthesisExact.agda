{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTExteriorRepulsionRouteSynthesisExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.GRQFTLocalizedDefocusingExteriorNoGoMaxCutExact as NoGoCut
import DASHI.Physics.Foundations.GRQFTPositiveDensityExteriorRepulsionNoGoExact as NoGo
import DASHI.Physics.Foundations.GRQFTSchwarzschildDeSitterExteriorEscapeExact as Kottler

------------------------------------------------------------------------
-- CURRENT EXTERIOR-REPULSION ROUTE SYNTHESIS
--
-- Standard static positive-density + vacuum Schwarzschild exterior:
--   blocked.
--
-- Positive-mass non-vacuum Kottler exterior:
--   explicit outward rational fixture constructed.
------------------------------------------------------------------------

data ExteriorRepulsionRouteStatus : Set where
  standardVacuumBlocked : ExteriorRepulsionRouteStatus
  nonVacuumKottlerConstructed : ExteriorRepulsionRouteStatus

standardVacuumRouteStatus :
  ExteriorRepulsionRouteStatus
standardVacuumRouteStatus = standardVacuumBlocked

nonVacuumKottlerRouteStatus :
  ExteriorRepulsionRouteStatus
nonVacuumKottlerRouteStatus = nonVacuumKottlerConstructed

record ExteriorRepulsionRouteSynthesis : Set where
  constructor exterior-repulsion-route-synthesis
  field
    authoritativeNoGo :
      NoGoCut.LocalizedDefocusingExteriorNoGoMaxCut

    positiveMassNonVacuumEscape :
      Kottler.PositiveMassNonVacuumExteriorRepulsionWitness

    standardVacuumRepulsion :
      Bool
    standardVacuumRepulsionIsFalse :
      standardVacuumRepulsion ≡ false

    nonVacuumPositiveMassRepulsion :
      Bool
    nonVacuumPositiveMassRepulsionIsTrue :
      nonVacuumPositiveMassRepulsion ≡ true

    selectedEscapeRoute :
      NoGo.ExteriorRepulsionEscapeRoute
    selectedEscapeRouteIsNonVacuum :
      selectedEscapeRoute ≡ NoGo.nonVacuumExteriorStress

open ExteriorRepulsionRouteSynthesis public

canonicalExteriorRepulsionRouteSynthesis :
  ExteriorRepulsionRouteSynthesis
canonicalExteriorRepulsionRouteSynthesis =
  exterior-repulsion-route-synthesis
    NoGoCut.canonicalLocalizedDefocusingExteriorNoGoMaxCut
    Kottler.canonicalPositiveMassNonVacuumExteriorRepulsionWitness
    false
    refl
    true
    refl
    NoGo.nonVacuumExteriorStress
    refl

record ExteriorRepulsionRouteSynthesisBoundary : Set where
  constructor exterior-repulsion-route-synthesis-boundary
  field
    positiveMassVacuumExteriorRepulsionBlocked : Bool
    positiveMassNonVacuumExteriorRepulsionConstructed : Bool
    negativeMetricMassRequiredForCurrentConstructedEscape : Bool
    interiorExteriorJunctionStillOpen : Bool
    SIPhysicalScaleStillOpen : Bool

canonicalExteriorRepulsionRouteSynthesisBoundary :
  ExteriorRepulsionRouteSynthesisBoundary
canonicalExteriorRepulsionRouteSynthesisBoundary =
  exterior-repulsion-route-synthesis-boundary
    true true false true true
