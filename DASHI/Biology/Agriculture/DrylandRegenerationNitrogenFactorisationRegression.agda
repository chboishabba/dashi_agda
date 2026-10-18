module DASHI.Biology.Agriculture.DrylandRegenerationNitrogenFactorisationRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
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


transportRouteRepairFactors :
  INF.FactorsThrough P.transportRouteEnrichedProjection P.transportRouteOutcome
transportRouteRepairFactors =
  P.transportRouteEnrichedFactorisation

demandTimingRepairFactors :
  INF.FactorsThrough P.releaseTimingEnrichedProjection P.demandCaptureOutcome
demandTimingRepairFactors =
  P.releaseTimingEnrichedFactorisation

waterStateRepairFactors :
  INF.FactorsThrough P.nitrogenWaterEnrichedProjection P.waterCoupledOutcome
waterStateRepairFactors =
  P.nitrogenWaterEnrichedFactorisation

counterfactualRepairFactors :
  INF.FactorsThrough P.replacementCounterfactualEnrichedProjection P.replacementOutcome
counterfactualRepairFactors =
  P.replacementCounterfactualEnrichedFactorisation
