module DASHI.Physics.Closure.NSTriadKNResidualCountingMagnitudeTheorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Nat using (ℕ; _+_) renaming (_≤_ to _≤ℕ_)

open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using ( NSTriadKNPairIncidenceProfileDecompositionModel
        ; Shell
        )

------------------------------------------------------------------------
-- Residual counting/magnitude theorem surface.
--
-- The residual lane may close either by a domination theorem or by its own
-- row/column exponent route. Both are carried explicitly here.

record NSTriadKNResidualCountingMagnitudeTheoremModel
    {ℓS ℓE ℓW ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓW ⊔ ℓV ⊔ ℓR)) where
  field
    decompositionModel :
      NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}

    Weight : Set ℓW
    weightAt : Shell decompositionModel -> Weight

    Bound : Set ℓV
    _≤_ : Bound -> Bound -> Set ℓR
    _*_ : Bound -> Bound -> Bound

    residualRowFunctional :
      Shell decompositionModel -> Weight -> Bound

    residualColumnFunctional :
      Shell decompositionModel -> Weight -> Bound

    residualRowTarget :
      Shell decompositionModel -> Bound

    residualColumnTarget :
      Shell decompositionModel -> Bound

    residualProductTarget :
      Shell decompositionModel -> Bound

    residualRowDecayExponent :
      Shell decompositionModel -> ℕ

    residualColumnDecayExponent :
      Shell decompositionModel -> ℕ

    residualRowAlphaBound :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_ (residualRowFunctional N wN)
          (residualRowTarget N)

    residualColumnBetaBound :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_ (residualColumnFunctional N wN)
          (residualColumnTarget N)

    residualExponentSumAtLeastTwo :
      (N : Shell decompositionModel) ->
      2 ≤ℕ (residualRowDecayExponent N + residualColumnDecayExponent N)

    residualWeightedProductFromExponents :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_ (_*_ (residualRowFunctional N wN)
               (residualColumnFunctional N wN))
          (residualProductTarget N)

    residualWeightedProductFromDomination :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_ (_*_ (residualRowFunctional N wN)
               (residualColumnFunctional N wN))
          (residualProductTarget N)

open NSTriadKNResidualCountingMagnitudeTheoremModel public
