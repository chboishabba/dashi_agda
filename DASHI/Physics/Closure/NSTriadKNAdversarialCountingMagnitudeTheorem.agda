module DASHI.Physics.Closure.NSTriadKNAdversarialCountingMagnitudeTheorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)

open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using ( NSTriadKNPairIncidenceProfileDecompositionModel
        ; Shell
        )

------------------------------------------------------------------------
-- Uniform adversarial counting/magnitude theorem surface.
--
-- Intended theorem chain:
--
--   adversarialRowN2Bound :
--     R_N^adv(w_N) <= A_adv / N^2
--
--   adversarialColumnN1Bound :
--     C_N^adv(w_N) <= B_adv / N
--
--   adversarialWeightedProductFromRowColumn :
--     R_N^adv(w_N) * C_N^adv(w_N) <= C_adv^2 / N^2
--
-- The row/column exponents intentionally over-close the Stage 3 target.

record NSTriadKNAdversarialCountingMagnitudeTheoremModel
    {ℓS ℓE ℓW ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓW ⊔ ℓV ⊔ ℓR)) where
  field
    decompositionModel :
      NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}

    Weight : Set ℓW
    weightAt : Shell decompositionModel -> Weight

    Bound : Set ℓV
    _≤_ : Bound -> Bound -> Set ℓR
    _*_ : Bound -> Bound -> Bound

    adversarialRowFunctional :
      Shell decompositionModel -> Weight -> Bound

    adversarialColumnFunctional :
      Shell decompositionModel -> Weight -> Bound

    adversarialRowTarget :
      Shell decompositionModel -> Bound

    adversarialColumnTarget :
      Shell decompositionModel -> Bound

    adversarialProductTarget :
      Shell decompositionModel -> Bound

    adversarialRowN2Bound :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_ (adversarialRowFunctional N wN)
          (adversarialRowTarget N)

    adversarialColumnN1Bound :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_ (adversarialColumnFunctional N wN)
          (adversarialColumnTarget N)

    adversarialWeightedProductFromRowColumn :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_ (_*_ (adversarialRowFunctional N wN)
               (adversarialColumnFunctional N wN))
          (adversarialProductTarget N)

open NSTriadKNAdversarialCountingMagnitudeTheoremModel public
