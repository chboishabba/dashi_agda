module DASHI.Physics.Closure.NSTriadKNTransitionWeightedProductBound where

open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Physics.Closure.NSTriadKNTransitionCountingMagnitudeTheorem
  as CountingMagnitude
open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using (Shell)

open import DASHI.Physics.Closure.NSTriadKNTransitionCountingMagnitudeTheorem
  using ( NSTriadKNTransitionCountingMagnitudeTheoremModel
        ; Bound
        ; _≤_
        ; _*_
        ; transitionColumnFunctional
        ; transitionProductTarget
        ; transitionRowFunctional
        ; transitionWeightedProductFromRowColumn
        ; weightAt
        )
open import DASHI.Physics.Closure.NSTriadKNTransitionWeightedProductBoundReceipt
  using ( NSTriadKNTransitionWeightedProductBoundReceipt
        ; canonicalNSTriadKNTransitionWeightedProductBoundReceipt
        )

------------------------------------------------------------------------
-- Uniform transition weighted-product theorem surface.
--
-- This is the theorem-shaped wrapper around the transition row/column route.

record NSTriadKNTransitionWeightedProductBoundModel
    {ℓS ℓE ℓW ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓW ⊔ ℓV ⊔ ℓR)) where
  field
    countingMagnitudeModel :
      NSTriadKNTransitionCountingMagnitudeTheoremModel
        {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}

    transitionTargetBound :
      Shell (CountingMagnitude.decompositionModel countingMagnitudeModel) ->
      Bound countingMagnitudeModel

    transitionWeightedProductBound :
      (N : Shell (CountingMagnitude.decompositionModel countingMagnitudeModel)) ->
      let wN = weightAt countingMagnitudeModel N in
      _≤_ countingMagnitudeModel
        (_*_ countingMagnitudeModel
           (transitionRowFunctional countingMagnitudeModel N wN)
           (transitionColumnFunctional countingMagnitudeModel N wN))
        (transitionTargetBound N)

open NSTriadKNTransitionWeightedProductBoundModel public

weightedDecompositionModel :
  ∀ {ℓS ℓE ℓW ℓV ℓR} ->
  NSTriadKNTransitionWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR} ->
  _
weightedDecompositionModel m =
  CountingMagnitude.decompositionModel
    (countingMagnitudeModel m)

transitionWeightedProductBoundReceipt :
  NSTriadKNTransitionWeightedProductBoundReceipt
transitionWeightedProductBoundReceipt =
  canonicalNSTriadKNTransitionWeightedProductBoundReceipt

transitionUniformProductTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNTransitionWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (weightedDecompositionModel m)) ->
  let wN = weightAt (countingMagnitudeModel m) N in
  _≤_ (countingMagnitudeModel m)
    (_*_ (countingMagnitudeModel m)
      (transitionRowFunctional (countingMagnitudeModel m) N wN)
      (transitionColumnFunctional (countingMagnitudeModel m) N wN))
    (transitionTargetBound m N)
transitionUniformProductTheorem m =
  transitionWeightedProductBound m

transitionProductRouteAvailable :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNTransitionWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (weightedDecompositionModel m)) ->
  let wN = weightAt (countingMagnitudeModel m) N in
  _≤_ (countingMagnitudeModel m)
    (_*_ (countingMagnitudeModel m)
      (transitionRowFunctional (countingMagnitudeModel m) N wN)
      (transitionColumnFunctional (countingMagnitudeModel m) N wN))
    (transitionProductTarget (countingMagnitudeModel m) N)
transitionProductRouteAvailable m =
  transitionWeightedProductFromRowColumn (countingMagnitudeModel m)
