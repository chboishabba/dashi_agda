module DASHI.Physics.Closure.NSPeriodicConcreteRouteDecision where

open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- Fail-closed route decisions forced by the exact and Galerkin falsifiers.
------------------------------------------------------------------------

data FarLowRoute : Set where
  fullOfficialNormSchurRoute : FarLowRoute

data FiveHalvesRoute : Set where
  timeIntegratedExpenditureRoute : FiveHalvesRoute

data PacketBoundaryRoute : Set where
  normalizedOrAdaptivePacketRoute : PacketBoundaryRoute

data CoverageRoute : Set where
  normalizedChartOrDiffuseBKMRoute : CoverageRoute

selectedFarLowRoute : FarLowRoute
selectedFarLowRoute = fullOfficialNormSchurRoute

selectedFiveHalvesRoute : FiveHalvesRoute
selectedFiveHalvesRoute = timeIntegratedExpenditureRoute

selectedPacketBoundaryRoute : PacketBoundaryRoute
selectedPacketBoundaryRoute = normalizedOrAdaptivePacketRoute

selectedCoverageRoute : CoverageRoute
selectedCoverageRoute = normalizedChartOrDiffuseBKMRoute

rawMultiplierAloneAcceptedAsFarLowProof : Bool
rawMultiplierAloneAcceptedAsFarLowProof = false

staticCompactGammaAdjacentContractionAccepted : Bool
staticCompactGammaAdjacentContractionAccepted = false

absolutePacketEnergyFloorAccepted : Bool
absolutePacketEnergyFloorAccepted = false

finiteHysteresisTraceAcceptedAsUniversalCoverage : Bool
finiteHysteresisTraceAcceptedAsUniversalCoverage = false

routeDecisionUsesNegativeEvidence : Bool
routeDecisionUsesNegativeEvidence = true

selectedRoutesInhabitedOnOfficialCarrier : Bool
selectedRoutesInhabitedOnOfficialCarrier = false
