module DASHI.Physics.Closure.NSTriadKNTransitionCountingMagnitudeTheorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Nat using (ℕ; _+_) renaming (_≤_ to _≤ℕ_)

open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using ( NSTriadKNPairIncidenceProfileDecompositionModel
        ; Shell
        )

------------------------------------------------------------------------
-- Uniform transition counting/magnitude theorem surface.
--
-- Intended theorem chain:
--
--   transitionRowAlphaBound :
--     R_N^trans(w_N) <= A_trans / N^alpha
--
--   transitionColumnBetaBound :
--     C_N^trans(w_N) <= B_trans / N^beta
--
--   transitionExponentSumAtLeastTwo :
--     alpha + beta >= 2
--
--   transitionWeightedProductFromExponents :
--     R_N^trans(w_N) * C_N^trans(w_N) <= C_trans^2 / N^2
--
-- The row/column exponents remain abstract here, but the arithmetic witness
-- alpha + beta >= 2 is carried explicitly rather than being left implicit.

record NSTriadKNTransitionCountingMagnitudeTheoremModel
    {ℓS ℓE ℓW ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓW ⊔ ℓV ⊔ ℓR)) where
  field
    decompositionModel :
      NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}

    Weight : Set ℓW
    weightAt : Shell decompositionModel -> Weight

    Bound : Set ℓV
    _≤_ : Bound -> Bound -> Set ℓR
    _*_ : Bound -> Bound -> Bound

    transitionRowFunctional :
      Shell decompositionModel -> Weight -> Bound

    transitionColumnFunctional :
      Shell decompositionModel -> Weight -> Bound

    transitionRowTarget :
      Shell decompositionModel -> Bound

    transitionColumnTarget :
      Shell decompositionModel -> Bound

    transitionProductTarget :
      Shell decompositionModel -> Bound

    transitionRowDecayExponent :
      Shell decompositionModel -> ℕ

    transitionColumnDecayExponent :
      Shell decompositionModel -> ℕ

    transitionRowAlphaBound :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_ (transitionRowFunctional N wN)
          (transitionRowTarget N)

    transitionColumnBetaBound :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_ (transitionColumnFunctional N wN)
          (transitionColumnTarget N)

    transitionExponentSumAtLeastTwo :
      (N : Shell decompositionModel) ->
      2 ≤ℕ (transitionRowDecayExponent N + transitionColumnDecayExponent N)

    transitionWeightedProductFromExponents :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_ (_*_ (transitionRowFunctional N wN)
               (transitionColumnFunctional N wN))
          (transitionProductTarget N)

open NSTriadKNTransitionCountingMagnitudeTheoremModel public

transitionWeightedProductFromRowColumn :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNTransitionCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  let wN = weightAt m N in
  _≤_ m (_*_ m (transitionRowFunctional m N wN)
               (transitionColumnFunctional m N wN))
        (transitionProductTarget m N)
transitionWeightedProductFromRowColumn m =
  transitionWeightedProductFromExponents m
