module DASHI.Physics.Closure.NSTriadKNResidualWeightedProductBound where

open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Physics.Closure.NSTriadKNResidualCountingMagnitudeTheorem
  as CountingMagnitude
open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using (Shell)
open import DASHI.Physics.Closure.NSTriadKNResidualCountingMagnitudeTheorem
  using ( NSTriadKNResidualCountingMagnitudeTheoremModel
        ; Bound
        ; _≤_
        ; _*_
        ; residualColumnFunctional
        ; residualProductTarget
        ; residualRowFunctional
        ; residualWeightedProductFromDomination
        ; residualWeightedProductFromExponents
        ; weightAt
        )

------------------------------------------------------------------------
-- Uniform residual weighted-product theorem surface.
--
-- This wrapper carries both allowed closure routes:
--
--   residualWeightedProductFromDomination
--   residualWeightedProductFromExponents

record NSTriadKNResidualWeightedProductBoundModel
    {ℓS ℓE ℓW ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓW ⊔ ℓV ⊔ ℓR)) where
  field
    countingMagnitudeModel :
      NSTriadKNResidualCountingMagnitudeTheoremModel
        {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}

    residualTargetBound :
      Shell (CountingMagnitude.decompositionModel countingMagnitudeModel) ->
      Bound countingMagnitudeModel

    residualWeightedProductBound :
      (N : Shell (CountingMagnitude.decompositionModel countingMagnitudeModel)) ->
      let wN = weightAt countingMagnitudeModel N in
      _≤_ countingMagnitudeModel
        (_*_ countingMagnitudeModel
           (residualRowFunctional countingMagnitudeModel N wN)
           (residualColumnFunctional countingMagnitudeModel N wN))
        (residualTargetBound N)

open NSTriadKNResidualWeightedProductBoundModel public

weightedDecompositionModel :
  ∀ {ℓS ℓE ℓW ℓV ℓR} ->
  NSTriadKNResidualWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR} ->
  _
weightedDecompositionModel m =
  CountingMagnitude.decompositionModel
    (countingMagnitudeModel m)

residualUniformProductTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNResidualWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (weightedDecompositionModel m)) ->
  let wN = weightAt (countingMagnitudeModel m) N in
  _≤_ (countingMagnitudeModel m)
    (_*_ (countingMagnitudeModel m)
      (residualRowFunctional (countingMagnitudeModel m) N wN)
      (residualColumnFunctional (countingMagnitudeModel m) N wN))
    (residualTargetBound m N)
residualUniformProductTheorem m =
  residualWeightedProductBound m

residualProductRouteFromExponents :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNResidualWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (weightedDecompositionModel m)) ->
  let wN = weightAt (countingMagnitudeModel m) N in
  _≤_ (countingMagnitudeModel m)
    (_*_ (countingMagnitudeModel m)
      (residualRowFunctional (countingMagnitudeModel m) N wN)
      (residualColumnFunctional (countingMagnitudeModel m) N wN))
    (residualProductTarget (countingMagnitudeModel m) N)
residualProductRouteFromExponents m =
  residualWeightedProductFromExponents (countingMagnitudeModel m)

residualProductRouteFromDomination :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNResidualWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (weightedDecompositionModel m)) ->
  let wN = weightAt (countingMagnitudeModel m) N in
  _≤_ (countingMagnitudeModel m)
    (_*_ (countingMagnitudeModel m)
      (residualRowFunctional (countingMagnitudeModel m) N wN)
      (residualColumnFunctional (countingMagnitudeModel m) N wN))
    (residualProductTarget (countingMagnitudeModel m) N)
residualProductRouteFromDomination m =
  residualWeightedProductFromDomination (countingMagnitudeModel m)
