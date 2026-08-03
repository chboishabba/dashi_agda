module DASHI.Physics.Closure.NSTriadKNWeightedSchurPhysicalFluxReuseExact where

------------------------------------------------------------------------
-- PURPOSE
-- Record exactly what the existing weighted-Schur development contributes to
-- the Luo flux route.  The abstract four-profile Schur algebra is closed.  The
-- concrete matrix/operator gate remains false because the exact physical
-- pair-incidence kernel has not yet been supplied.  Once a physical
-- `PhysicalCutoffFluxWeightedSchurBridge` is inhabited, the Luo-shaped flux
-- estimate is an immediate theorem.
--
-- Primary source for the Schur mechanism:
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal/year: Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (_≤_; _*_)

import DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound as WeightedSchur
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact as Flux

weightedSchurPhysicalFluxEstimate :
  (bridge : Flux.PhysicalCutoffFluxWeightedSchurBridge) →
  Flux.absoluteCutoffFlux bridge
    ≤ Flux.profileSchurConstant bridge
      * (Flux.cutoffEnergyMajorant bridge
        * Flux.lowPassGradientInfinity bridge)
weightedSchurPhysicalFluxEstimate = Flux.luoCutoffFluxEstimate

record WeightedSchurPhysicalFluxReuseReceipt : Set where
  constructor receipt
  field
    abstractProfileWeightedSchurAlgebraClosed :
      WeightedSchur.weightedSchurProductBoundClosed ≡ true

    concretePhysicalKernelWeightedSchurDataOpen :
      WeightedSchur.weightedSchurMatrixOperatorDataClosed ≡ false

    concretePhysicalOperatorWitnessOpen :
      WeightedSchur.actualUnitShellWeightedSchurOperatorWitnessClosed ≡ false

    fluxCompositionTheoremConstructed :
      Flux.weightedSchurToLuoFluxCompositionConstructed ≡ true

    physicalFluxBridgeStillOpen :
      Flux.physicalWeightedSchurBridgeInhabited ≡ false

open WeightedSchurPhysicalFluxReuseReceipt public

weightedSchurPhysicalFluxReuseReceipt :
  WeightedSchurPhysicalFluxReuseReceipt
weightedSchurPhysicalFluxReuseReceipt = receipt
  WeightedSchur.weightedSchurProductBoundClosedIsTrue
  WeightedSchur.weightedSchurMatrixOperatorDataClosedIsFalse
  WeightedSchur.actualUnitShellWeightedSchurOperatorWitnessClosedIsFalse
  Flux.weightedSchurToLuoFluxCompositionConstructedIsTrue
  Flux.physicalWeightedSchurBridgeInhabitedIsFalse

weightedSchurRelevantToLuoFluxRoute : Bool
weightedSchurRelevantToLuoFluxRoute = true

weightedSchurPhysicalIdentificationComplete : Bool
weightedSchurPhysicalIdentificationComplete = false

weightedSchurRelevantToLuoFluxRouteIsTrue :
  weightedSchurRelevantToLuoFluxRoute ≡ true
weightedSchurRelevantToLuoFluxRouteIsTrue = refl

weightedSchurPhysicalIdentificationCompleteIsFalse :
  weightedSchurPhysicalIdentificationComplete ≡ false
weightedSchurPhysicalIdentificationCompleteIsFalse = refl
