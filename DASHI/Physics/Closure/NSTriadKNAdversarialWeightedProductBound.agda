module DASHI.Physics.Closure.NSTriadKNAdversarialWeightedProductBound where

open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Physics.Closure.NSTriadKNAdversarialCountingMagnitudeTheorem as CountingMagnitude
open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using (Shell)

open import DASHI.Physics.Closure.NSTriadKNAdversarialCountingMagnitudeTheorem
  using ( NSTriadKNAdversarialCountingMagnitudeTheoremModel
        ; Bound
        ; _≤_
        ; _*_
        ; adversarialColumnFunctional
        ; adversarialProductTarget
        ; adversarialRowFunctional
        ; adversarialWeightedProductFromRowColumn
        ; weightAt
        )
open import DASHI.Physics.Closure.NSTriadKNAdversarialWeightedProductBoundReceipt
  using ( NSTriadKNAdversarialWeightedProductBoundReceipt
        ; canonicalNSTriadKNAdversarialWeightedProductBoundReceipt
        )

------------------------------------------------------------------------
-- Uniform adversarial weighted-product theorem surface.
--
-- This is the theorem-shaped wrapper around the adversarial row/column route.

record NSTriadKNAdversarialWeightedProductBoundModel
    {ℓS ℓE ℓW ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓW ⊔ ℓV ⊔ ℓR)) where
  field
    countingMagnitudeModel :
      NSTriadKNAdversarialCountingMagnitudeTheoremModel
        {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}

    adversarialTargetBound :
      Shell (CountingMagnitude.decompositionModel countingMagnitudeModel) ->
      Bound countingMagnitudeModel

    adversarialWeightedProductBound :
      (N : Shell (CountingMagnitude.decompositionModel countingMagnitudeModel)) ->
      let wN = weightAt countingMagnitudeModel N in
      _≤_ countingMagnitudeModel
        (_*_ countingMagnitudeModel
           (adversarialRowFunctional countingMagnitudeModel N wN)
           (adversarialColumnFunctional countingMagnitudeModel N wN))
        (adversarialTargetBound N)

open NSTriadKNAdversarialWeightedProductBoundModel public

weightedDecompositionModel :
  ∀ {ℓS ℓE ℓW ℓV ℓR} ->
  NSTriadKNAdversarialWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR} ->
  _
weightedDecompositionModel m =
  CountingMagnitude.decompositionModel
    (countingMagnitudeModel m)

adversarialWeightedProductBoundReceipt :
  NSTriadKNAdversarialWeightedProductBoundReceipt
adversarialWeightedProductBoundReceipt =
  canonicalNSTriadKNAdversarialWeightedProductBoundReceipt

adversarialUniformProductTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNAdversarialWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (weightedDecompositionModel m)) ->
  let wN = weightAt (countingMagnitudeModel m) N in
  _≤_ (countingMagnitudeModel m)
    (_*_ (countingMagnitudeModel m)
      (adversarialRowFunctional (countingMagnitudeModel m) N wN)
      (adversarialColumnFunctional (countingMagnitudeModel m) N wN))
    (adversarialTargetBound m N)
adversarialUniformProductTheorem m =
  adversarialWeightedProductBound m

adversarialProductRouteAvailable :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNAdversarialWeightedProductBoundModel {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (weightedDecompositionModel m)) ->
  let wN = weightAt (countingMagnitudeModel m) N in
  _≤_ (countingMagnitudeModel m)
    (_*_ (countingMagnitudeModel m)
      (adversarialRowFunctional (countingMagnitudeModel m) N wN)
      (adversarialColumnFunctional (countingMagnitudeModel m) N wN))
    (adversarialProductTarget (countingMagnitudeModel m) N)
adversarialProductRouteAvailable m =
  adversarialWeightedProductFromRowColumn (countingMagnitudeModel m)
