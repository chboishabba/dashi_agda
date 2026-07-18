module DASHI.Physics.Closure.NSTriadKNForcedTailWeightedProductBound where

open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Physics.Closure.NSTriadKNForcedTailCountingMagnitudeTheorem as CountingMagnitude

open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using ( Shell )

open import DASHI.Physics.Closure.NSTriadKNForcedTailCountingMagnitudeTheorem
  using ( NSTriadKNForcedTailCountingMagnitudeTheoremModel
        ; Bound
        ; _≤_
        ; _*_
        ; forcedTailColumnFunctional
        ; forcedTailProductConclusion
        ; forcedTailProductTarget
        ; forcedTailRowFunctional
        ; weightAt
        )
open import DASHI.Physics.Closure.NSTriadKNForcedTailWeightedProductBoundReceipt
  using ( NSTriadKNForcedTailWeightedProductBoundReceipt
        ; canonicalNSTriadKNForcedTailWeightedProductBoundReceipt
        )

------------------------------------------------------------------------
-- Uniform forced-tail weighted-product theorem surface.
--
-- The receipt layer records sampled N=6,8,10,12 evidence. This module names
-- the actual forced-tail product theorem after the row/column counting-
-- magnitude route has been set up explicitly.

record NSTriadKNForcedTailWeightedProductBoundModel
    {ℓS ℓE ℓW ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓW ⊔ ℓV ⊔ ℓR)) where
  field
    countingMagnitudeModel :
      NSTriadKNForcedTailCountingMagnitudeTheoremModel
        {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}

    forcedTailTargetBound :
      Shell (CountingMagnitude.decompositionModel countingMagnitudeModel) ->
      Bound countingMagnitudeModel

    forcedTailWeightedProductBound :
      (N : Shell (CountingMagnitude.decompositionModel countingMagnitudeModel)) ->
      let wN = weightAt countingMagnitudeModel N in
      _≤_ countingMagnitudeModel
        (_*_ countingMagnitudeModel
           (forcedTailRowFunctional countingMagnitudeModel N wN)
           (forcedTailColumnFunctional countingMagnitudeModel N wN))
        (forcedTailTargetBound N)

open NSTriadKNForcedTailWeightedProductBoundModel public

weightedDecompositionModel :
  ∀ {ℓS ℓE ℓW ℓV ℓR} ->
  NSTriadKNForcedTailWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR} ->
  _
weightedDecompositionModel m =
  CountingMagnitude.decompositionModel
    (countingMagnitudeModel m)

forcedTailWeightedProductBoundReceipt :
  NSTriadKNForcedTailWeightedProductBoundReceipt
forcedTailWeightedProductBoundReceipt =
  canonicalNSTriadKNForcedTailWeightedProductBoundReceipt

forcedTailUniformProductTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (weightedDecompositionModel m)) ->
  let wN = weightAt (countingMagnitudeModel m) N in
  _≤_ (countingMagnitudeModel m)
    (_*_ (countingMagnitudeModel m)
      (forcedTailRowFunctional (countingMagnitudeModel m) N wN)
      (forcedTailColumnFunctional (countingMagnitudeModel m) N wN))
    (forcedTailTargetBound m N)
forcedTailUniformProductTheorem m =
  forcedTailWeightedProductBound m

forcedTailProductRouteAvailable :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (weightedDecompositionModel m)) ->
  let wN = weightAt (countingMagnitudeModel m) N in
  _≤_ (countingMagnitudeModel m)
    (_*_ (countingMagnitudeModel m)
      (forcedTailRowFunctional (countingMagnitudeModel m) N wN)
      (forcedTailColumnFunctional (countingMagnitudeModel m) N wN))
    (forcedTailProductTarget (countingMagnitudeModel m) N)
forcedTailProductRouteAvailable m =
  forcedTailProductConclusion (countingMagnitudeModel m)
