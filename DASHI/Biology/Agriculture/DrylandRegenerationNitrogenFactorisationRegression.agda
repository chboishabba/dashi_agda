module DASHI.Biology.Agriculture.DrylandRegenerationNitrogenFactorisationRegression where

open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery
import DASHI.Biology.Agriculture.DrylandRegenerationNitrogenFactorisationExact as P

fixedNDoesNotDetermineRoute :
  INF.FactorsThrough P.fixedNitrogenProjection P.transportRouteOutcome → ⊥
fixedNDoesNotDetermineRoute =
  P.fixedNitrogenCannotDetermineTransportRoute

releasedNDoesNotDetermineDemandCapture :
  INF.FactorsThrough P.releasedNitrogenProjection P.demandCaptureOutcome → ⊥
releasedNDoesNotDetermineDemandCapture =
  P.releasedNitrogenCannotDetermineDemandCapture

nitrogenServiceDoesNotEraseWater :
  INF.FactorsThrough P.nitrogenServiceProjection P.waterCoupledOutcome → ⊥
nitrogenServiceDoesNotEraseWater =
  P.nitrogenServiceCannotDetermineWaterCoupledOutcome

carryoverDoesNotDetermineReplacement :
  INF.FactorsThrough P.carryoverProjection P.replacementOutcome → ⊥
carryoverDoesNotDetermineReplacement =
  P.carryoverCannotDetermineReplacementValue

routeAxisWasDiscoveredByFailedFactorisation :
  Discovery.route P.transportRouteAxisProposal ≡ Discovery.failedFactorsThrough
routeAxisWasDiscoveredByFailedFactorisation = refl

counterfactualAxisTargetsExperiment :
  Discovery.route P.mineralNCounterfactualAxisProposal ≡ Discovery.experimentalDesign
counterfactualAxisTargetsExperiment = refl
