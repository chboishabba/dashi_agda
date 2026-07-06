module DASHI.Physics.Closure.NSTriadKNForcedTailCountingMagnitudeTheorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)

open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using ( NSTriadKNPairIncidenceProfileDecompositionModel
        ; Shell
        )

------------------------------------------------------------------------
-- Uniform forced-tail counting/magnitude theorem surface.
--
-- This is the missing analytic upgrade from sampled forced-tail telemetry to
-- a theorem-shaped statement. The intended route is:
--
--   row bound:    R_N^FT(w_N) <= A_FT
--   column classes: tail-end / near-tail / transition-facing / degenerate
--   column split: multiplicity bound * magnitude bound <= B_FT / N^2
--   column bound: C_N^FT(w_N) <= B_FT / N^2
--
-- so that the forced-tail weighted-product conclusion closes on the target
-- N^-2 scale. This module names that theorem surface without claiming it is
-- inhabited in the current repo state.

record NSTriadKNForcedTailCountingMagnitudeTheoremModel
    {ℓS ℓE ℓW ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓW ⊔ ℓV ⊔ ℓR)) where
  field
    decompositionModel :
      NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}

    Weight : Set ℓW
    weightAt : Shell decompositionModel -> Weight

    Column : Set ℓE
    ForcedTailIncidence : Set ℓE
    ForcedTailColumnClass : Set ℓE
    ForcedTailClassParameter :
      Shell decompositionModel -> ForcedTailColumnClass -> Column -> Set ℓE
    ForcedTailClassParameterHead :
      Shell decompositionModel -> ForcedTailColumnClass -> Column -> Set ℓE
    ForcedTailClassParameterTail :
      (N : Shell decompositionModel) ->
      (c : ForcedTailColumnClass) ->
      (j : Column) ->
      ForcedTailClassParameterHead N c j -> Set ℓE

    Bound : Set ℓV
    _≤_ : Bound -> Bound -> Set ℓR
    _*_ : Bound -> Bound -> Bound
    ≤-trans :
      {a b c : Bound} ->
      _≤_ a b ->
      _≤_ b c ->
      _≤_ a c
    *-monoˡ-≤ :
      (a : Bound) ->
      {b c : Bound} ->
      _≤_ b c ->
      _≤_ (_*_ a b) (_*_ a c)

    forcedTailRowFunctional :
      Shell decompositionModel -> Weight -> Bound

    forcedTailColumnFunctional :
      Shell decompositionModel -> Weight -> Bound

    forcedTailRowUniformConstant : Bound
    forcedTailColumnMultiplicityBound :
      Shell decompositionModel -> Bound
    forcedTailColumnMagnitudeBound :
      Shell decompositionModel -> Bound
    forcedTailColumnWeightedSum :
      Shell decompositionModel -> Column -> Weight -> Bound
    forcedTailColumnMultiplicityProfile :
      Shell decompositionModel -> Column -> Bound
    forcedTailColumnMagnitudeProfile :
      Shell decompositionModel -> Column -> Bound
    forcedTailColumnProfileTarget :
      Shell decompositionModel -> Column -> Bound
    forcedTailIncidenceFamily :
      Shell decompositionModel -> Column -> ForcedTailIncidence -> Set ℓR
    forcedTailColumnMultiplicityCount :
      Shell decompositionModel -> Column -> Bound
    forcedTailColumnClass :
      Shell decompositionModel -> Column -> ForcedTailColumnClass
    forcedTailClassIncidenceFamily :
      Shell decompositionModel ->
      Column ->
      ForcedTailColumnClass ->
      ForcedTailIncidence -> Set ℓR
    forcedTailClassIncidenceEncoding :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      (c : ForcedTailColumnClass) ->
      (τ : ForcedTailIncidence) ->
      forcedTailClassIncidenceFamily N j c τ ->
      ForcedTailClassParameter N c j
    forcedTailColumnClassMultiplicityCount :
      Shell decompositionModel -> Column -> ForcedTailColumnClass -> Bound
    forcedTailClassIncidenceEncodingFiberConstant :
      ForcedTailColumnClass -> Bound
    forcedTailClassParameterHeadOf :
      (N : Shell decompositionModel) ->
      (c : ForcedTailColumnClass) ->
      (j : Column) ->
      ForcedTailClassParameter N c j ->
      ForcedTailClassParameterHead N c j
    forcedTailClassParameterTailOf :
      (N : Shell decompositionModel) ->
      (c : ForcedTailColumnClass) ->
      (j : Column) ->
      (a : ForcedTailClassParameter N c j) ->
      ForcedTailClassParameterTail N c j
        (forcedTailClassParameterHeadOf N c j a)
    forcedTailClassParameterHeadCount :
      Shell decompositionModel -> ForcedTailColumnClass -> Column -> Bound
    forcedTailClassParameterTailCount :
      (N : Shell decompositionModel) ->
      (c : ForcedTailColumnClass) ->
      (j : Column) ->
      ForcedTailClassParameterHead N c j -> Bound
    forcedTailClassParameterTailCountMax :
      Shell decompositionModel -> ForcedTailColumnClass -> Column -> Bound
    forcedTailClassParameterCount :
      Shell decompositionModel -> ForcedTailColumnClass -> Column -> Bound
    forcedTailClassParameterHeadBoundFormula :
      Shell decompositionModel -> ForcedTailColumnClass -> Bound
    forcedTailClassParameterTailBoundFormula :
      Shell decompositionModel -> ForcedTailColumnClass -> Bound
    forcedTailClassMultiplicityBoundFormula :
      Shell decompositionModel -> ForcedTailColumnClass -> Bound
    forcedTailColumnClassMultiplicityBound :
      Shell decompositionModel -> ForcedTailColumnClass -> Bound
    forcedTailMagnitudeAt :
      Shell decompositionModel -> ForcedTailIncidence -> Bound
    forcedTailMagnitudeNormalizationFactor :
      Shell decompositionModel -> ForcedTailIncidence -> Bound
    forcedTailMagnitudeCoefficientFactor :
      Shell decompositionModel -> ForcedTailIncidence -> Bound
    forcedTailMagnitudeProjectionFactor :
      Shell decompositionModel -> ForcedTailIncidence -> Bound
    forcedTailMagnitudeEnvelope :
      Shell decompositionModel -> ForcedTailIncidence -> Bound
    forcedTailClassNormalizationBoundFormula :
      Shell decompositionModel -> ForcedTailColumnClass -> Bound
    forcedTailClassCoefficientBoundFormula :
      Shell decompositionModel -> ForcedTailColumnClass -> Bound
    forcedTailClassProjectionBoundFormula :
      Shell decompositionModel -> ForcedTailColumnClass -> Bound
    forcedTailClassMagnitudeBoundFormula :
      Shell decompositionModel -> ForcedTailColumnClass -> Bound
    forcedTailColumnClassMagnitudeBound :
      Shell decompositionModel -> ForcedTailColumnClass -> Bound
    forcedTailN2Scale : Shell decompositionModel -> Bound
    forcedTailClassProductFormulaTarget :
      Shell decompositionModel -> ForcedTailColumnClass -> Bound
    forcedTailColumnClassProductTarget :
      Shell decompositionModel -> ForcedTailColumnClass -> Bound
    forcedTailColumnClassProductN2Constant :
      ForcedTailColumnClass -> Bound
    forcedTailColumnN2Target : Shell decompositionModel -> Bound
    forcedTailProductTarget : Shell decompositionModel -> Bound

    forcedTailRowUniformBound :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_ (forcedTailRowFunctional N wN)
          forcedTailRowUniformConstant

    forcedTailColumnMultiplicityLemma :
      (N : Shell decompositionModel) ->
      _≤_ (_*_ (forcedTailColumnMultiplicityBound N)
               (forcedTailColumnMagnitudeBound N))
          (forcedTailColumnN2Target N)

    forcedTailColumnMultiplicityProfileLemma :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailColumnMultiplicityProfile N j)
          (forcedTailColumnMultiplicityBound N)

    forcedTailColumnMultiplicityCountCoversProfile :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailColumnMultiplicityProfile N j)
          (forcedTailColumnMultiplicityCount N j)

    forcedTailColumnClassMultiplicityLemma :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailColumnClassMultiplicityCount N j
             (forcedTailColumnClass N j))
          (forcedTailClassMultiplicityBoundFormula N
             (forcedTailColumnClass N j))

    forcedTailClassMultiplicityFormulaControlsBound :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailClassMultiplicityBoundFormula N
             (forcedTailColumnClass N j))
          (forcedTailColumnClassMultiplicityBound N
             (forcedTailColumnClass N j))

    forcedTailClassMultiplicityCountCoversColumnCount :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailColumnMultiplicityCount N j)
          (forcedTailColumnClassMultiplicityCount N j
             (forcedTailColumnClass N j))

    forcedTailClassIncidenceEncodingFiberBound :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      (c : ForcedTailColumnClass) ->
      _≤_ (forcedTailColumnClassMultiplicityCount N j c)
          (_*_ (forcedTailClassIncidenceEncodingFiberConstant c)
               (forcedTailClassParameterCount N c j))

    forcedTailClassParameterCountBound :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      (c : ForcedTailColumnClass) ->
      _≤_ (forcedTailClassParameterCount N c j)
          (forcedTailClassMultiplicityBoundFormula N c)

    forcedTailClassParameterHeadCountBound :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      (c : ForcedTailColumnClass) ->
      _≤_ (forcedTailClassParameterHeadCount N c j)
          (forcedTailClassParameterHeadBoundFormula N c)

    forcedTailClassParameterTailCountBound :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      (c : ForcedTailColumnClass) ->
      (h : ForcedTailClassParameterHead N c j) ->
      _≤_ (forcedTailClassParameterTailCount N c j h)
          (forcedTailClassParameterTailCountMax N c j)

    forcedTailClassParameterTailCountMaxBound :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      (c : ForcedTailColumnClass) ->
      _≤_ (forcedTailClassParameterTailCountMax N c j)
          (forcedTailClassParameterTailBoundFormula N c)

    forcedTailClassParameterCountFactorization :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      (c : ForcedTailColumnClass) ->
      _≤_ (forcedTailClassParameterCount N c j)
          (_*_ (forcedTailClassParameterHeadCount N c j)
               (forcedTailClassParameterTailCountMax N c j))

    forcedTailHeadTailProductControlsMultiplicityFormula :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      (c : ForcedTailColumnClass) ->
      _≤_ (_*_ (forcedTailClassParameterHeadBoundFormula N c)
               (forcedTailClassParameterTailBoundFormula N c))
          (forcedTailClassMultiplicityBoundFormula N c)

    forcedTailColumnMagnitudeProfileLemma :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailColumnMagnitudeProfile N j)
          (forcedTailColumnMagnitudeBound N)

    forcedTailMagnitudeKernelUpperBound :
      (N : Shell decompositionModel) ->
      (τ : ForcedTailIncidence) ->
      _≤_ (forcedTailMagnitudeAt N τ)
          (forcedTailMagnitudeEnvelope N τ)

    forcedTailMagnitudeEnvelopeFactorization :
      (N : Shell decompositionModel) ->
      (τ : ForcedTailIncidence) ->
      _≤_ (forcedTailMagnitudeEnvelope N τ)
          (_*_ (forcedTailMagnitudeNormalizationFactor N τ)
               (_*_ (forcedTailMagnitudeCoefficientFactor N τ)
                    (forcedTailMagnitudeProjectionFactor N τ)))

    forcedTailColumnClassMagnitudeLemma :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailColumnMagnitudeProfile N j)
          (forcedTailClassMagnitudeBoundFormula N
             (forcedTailColumnClass N j))

    forcedTailMagnitudeEnvelopeClassBound :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      (τ : ForcedTailIncidence) ->
      forcedTailClassIncidenceFamily N j (forcedTailColumnClass N j) τ ->
      _≤_ (forcedTailMagnitudeEnvelope N τ)
          (forcedTailClassMagnitudeBoundFormula N
             (forcedTailColumnClass N j))

    forcedTailMagnitudeNormalizationClassBound :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      (τ : ForcedTailIncidence) ->
      forcedTailClassIncidenceFamily N j (forcedTailColumnClass N j) τ ->
      _≤_ (forcedTailMagnitudeNormalizationFactor N τ)
          (forcedTailClassNormalizationBoundFormula N
             (forcedTailColumnClass N j))

    forcedTailMagnitudeCoefficientClassBound :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      (τ : ForcedTailIncidence) ->
      forcedTailClassIncidenceFamily N j (forcedTailColumnClass N j) τ ->
      _≤_ (forcedTailMagnitudeCoefficientFactor N τ)
          (forcedTailClassCoefficientBoundFormula N
             (forcedTailColumnClass N j))

    forcedTailMagnitudeProjectionClassBound :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      (τ : ForcedTailIncidence) ->
      forcedTailClassIncidenceFamily N j (forcedTailColumnClass N j) τ ->
      _≤_ (forcedTailMagnitudeProjectionFactor N τ)
          (forcedTailClassProjectionBoundFormula N
             (forcedTailColumnClass N j))

    forcedTailClassEnvelopeProductControlsMagnitudeFormula :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (_*_ (forcedTailClassNormalizationBoundFormula N
                  (forcedTailColumnClass N j))
               (_*_ (forcedTailClassCoefficientBoundFormula N
                       (forcedTailColumnClass N j))
                    (forcedTailClassProjectionBoundFormula N
                       (forcedTailColumnClass N j))))
          (forcedTailClassMagnitudeBoundFormula N
             (forcedTailColumnClass N j))

    forcedTailClassMagnitudeFormulaControlsBound :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailClassMagnitudeBoundFormula N
             (forcedTailColumnClass N j))
          (forcedTailColumnClassMagnitudeBound N
             (forcedTailColumnClass N j))

    forcedTailColumnProfileProductLemma :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (_*_ (forcedTailColumnMultiplicityProfile N j)
               (forcedTailColumnMagnitudeProfile N j))
          (forcedTailColumnProfileTarget N j)

    forcedTailColumnClassProductLemma :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (_*_ (forcedTailClassMultiplicityBoundFormula N
                  (forcedTailColumnClass N j))
               (forcedTailClassMagnitudeBoundFormula N
                  (forcedTailColumnClass N j)))
          (forcedTailClassProductFormulaTarget N
             (forcedTailColumnClass N j))

    forcedTailClassProductFormulaN2Bound :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (_*_ (forcedTailN2Scale N)
               (_*_ (forcedTailClassMultiplicityBoundFormula N
                       (forcedTailColumnClass N j))
                    (forcedTailClassMagnitudeBoundFormula N
                       (forcedTailColumnClass N j))))
          (forcedTailColumnClassProductN2Constant
             (forcedTailColumnClass N j))

    forcedTailClassProductFormulaControlsTarget :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailClassProductFormulaTarget N
             (forcedTailColumnClass N j))
          (forcedTailColumnClassProductTarget N
             (forcedTailColumnClass N j))

    forcedTailClassFormulaMultiplicityControlsTarget :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailClassMultiplicityBoundFormula N
             (forcedTailColumnClass N j))
          (forcedTailColumnClassMultiplicityBound N
             (forcedTailColumnClass N j))

    forcedTailClassFormulaMagnitudeControlsTarget :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailClassMagnitudeBoundFormula N
             (forcedTailColumnClass N j))
          (forcedTailColumnClassMagnitudeBound N
             (forcedTailColumnClass N j))

    forcedTailColumnClassTargetProductLemma :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (_*_ (forcedTailColumnClassMultiplicityBound N
                  (forcedTailColumnClass N j))
               (forcedTailColumnClassMagnitudeBound N
                  (forcedTailColumnClass N j)))
          (forcedTailColumnClassProductTarget N
             (forcedTailColumnClass N j))

    forcedTailClassToColumnMultiplicityLift :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailColumnMultiplicityProfile N j)
          (forcedTailColumnClassMultiplicityBound N
             (forcedTailColumnClass N j))

    forcedTailClassToColumnMagnitudeLift :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailColumnMagnitudeProfile N j)
          (forcedTailColumnClassMagnitudeBound N
             (forcedTailColumnClass N j))

    forcedTailClassToColumnProductLift :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailColumnProfileTarget N j)
          (forcedTailColumnClassProductTarget N
             (forcedTailColumnClass N j))

    forcedTailColumnSumByMultiplicityMagnitude :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      let wN = weightAt N in
      _≤_ (forcedTailColumnWeightedSum N j wN)
          (_*_ (forcedTailColumnMultiplicityProfile N j)
               (forcedTailColumnMagnitudeProfile N j))

    forcedTailColumnToShellN2Lift :
      (N : Shell decompositionModel) ->
      (j : Column) ->
      _≤_ (forcedTailColumnClassProductTarget N
             (forcedTailColumnClass N j))
          (forcedTailColumnN2Target N)

    forcedTailColumnN2Bound :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_ (forcedTailColumnFunctional N wN)
          (forcedTailColumnN2Target N)

    forcedTailProductConclusion :
      (N : Shell decompositionModel) ->
      let wN = weightAt N in
      _≤_
        (_*_ (forcedTailRowFunctional N wN)
             (forcedTailColumnFunctional N wN))
        (forcedTailProductTarget N)

open NSTriadKNForcedTailCountingMagnitudeTheoremModel public

forcedTailRowUniformTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  let wN = weightAt m N in
  _≤_ m
    (forcedTailRowFunctional m N wN)
    (forcedTailRowUniformConstant m)
forcedTailRowUniformTheorem m =
  forcedTailRowUniformBound m

forcedTailColumnN2Theorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  let wN = weightAt m N in
  _≤_ m
    (forcedTailColumnFunctional m N wN)
    (forcedTailColumnN2Target m N)
forcedTailColumnN2Theorem m =
  forcedTailColumnN2Bound m

forcedTailColumnMultiplicityMagnitudeProductTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  _≤_ m
    (_*_ m
      (forcedTailColumnMultiplicityBound m N)
      (forcedTailColumnMagnitudeBound m N))
    (forcedTailColumnN2Target m N)
forcedTailColumnMultiplicityMagnitudeProductTheorem m =
  forcedTailColumnMultiplicityLemma m

forcedTailColumnMultiplicityProfileTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailColumnMultiplicityProfile m N j)
    (forcedTailColumnMultiplicityBound m N)
forcedTailColumnMultiplicityProfileTheorem m =
  forcedTailColumnMultiplicityProfileLemma m

forcedTailColumnMultiplicityCountCoversProfileTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailColumnMultiplicityProfile m N j)
    (forcedTailColumnMultiplicityCount m N j)
forcedTailColumnMultiplicityCountCoversProfileTheorem m =
  forcedTailColumnMultiplicityCountCoversProfile m

forcedTailClassMultiplicityCountCoversColumnCountTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailColumnMultiplicityCount m N j)
    (forcedTailColumnClassMultiplicityCount m N j
      (forcedTailColumnClass m N j))
forcedTailClassMultiplicityCountCoversColumnCountTheorem m =
  forcedTailClassMultiplicityCountCoversColumnCount m

forcedTailClassIncidenceEncodingFiberBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (c : ForcedTailColumnClass m) ->
  _≤_ m
    (forcedTailColumnClassMultiplicityCount m N j c)
    (_*_ m
      (forcedTailClassIncidenceEncodingFiberConstant m c)
      (forcedTailClassParameterCount m N c j))
forcedTailClassIncidenceEncodingFiberBoundTheorem m =
  forcedTailClassIncidenceEncodingFiberBound m

forcedTailClassParameterCountBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (c : ForcedTailColumnClass m) ->
  _≤_ m
    (forcedTailClassParameterCount m N c j)
    (forcedTailClassMultiplicityBoundFormula m N c)
forcedTailClassParameterCountBoundTheorem m =
  forcedTailClassParameterCountBound m

forcedTailClassParameterHeadCountBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (c : ForcedTailColumnClass m) ->
  _≤_ m
    (forcedTailClassParameterHeadCount m N c j)
    (forcedTailClassParameterHeadBoundFormula m N c)
forcedTailClassParameterHeadCountBoundTheorem m =
  forcedTailClassParameterHeadCountBound m

forcedTailClassParameterTailCountBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (c : ForcedTailColumnClass m) ->
  (h : ForcedTailClassParameterHead m N c j) ->
  _≤_ m
    (forcedTailClassParameterTailCount m N c j h)
    (forcedTailClassParameterTailCountMax m N c j)
forcedTailClassParameterTailCountBoundTheorem m =
  forcedTailClassParameterTailCountBound m

forcedTailClassParameterTailCountMaxBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (c : ForcedTailColumnClass m) ->
  _≤_ m
    (forcedTailClassParameterTailCountMax m N c j)
    (forcedTailClassParameterTailBoundFormula m N c)
forcedTailClassParameterTailCountMaxBoundTheorem m =
  forcedTailClassParameterTailCountMaxBound m

forcedTailClassParameterCountFactorizationTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (c : ForcedTailColumnClass m) ->
  _≤_ m
    (forcedTailClassParameterCount m N c j)
    (_*_ m
      (forcedTailClassParameterHeadCount m N c j)
      (forcedTailClassParameterTailCountMax m N c j))
forcedTailClassParameterCountFactorizationTheorem m =
  forcedTailClassParameterCountFactorization m

forcedTailHeadTailProductControlsMultiplicityFormulaTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (c : ForcedTailColumnClass m) ->
  _≤_ m
    (_*_ m
      (forcedTailClassParameterHeadBoundFormula m N c)
      (forcedTailClassParameterTailBoundFormula m N c))
    (forcedTailClassMultiplicityBoundFormula m N c)
forcedTailHeadTailProductControlsMultiplicityFormulaTheorem m =
  forcedTailHeadTailProductControlsMultiplicityFormula m

forcedTailClassEncodingCountBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (c : ForcedTailColumnClass m) ->
  _≤_ m
    (forcedTailColumnClassMultiplicityCount m N j c)
    (_*_ m
      (forcedTailClassIncidenceEncodingFiberConstant m c)
      (forcedTailClassMultiplicityBoundFormula m N c))
forcedTailClassEncodingCountBoundTheorem m N j c =
  ≤-trans m
    (forcedTailClassIncidenceEncodingFiberBound m N j c)
    (*-monoˡ-≤ m
      (forcedTailClassIncidenceEncodingFiberConstant m c)
      (forcedTailClassParameterCountBound m N j c))

forcedTailColumnClassMultiplicityTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailColumnClassMultiplicityCount m N j
      (forcedTailColumnClass m N j))
    (forcedTailClassMultiplicityBoundFormula m N
      (forcedTailColumnClass m N j))
forcedTailColumnClassMultiplicityTheorem m =
  forcedTailColumnClassMultiplicityLemma m

forcedTailColumnClassMultiplicityFromEncodingTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailColumnClassMultiplicityCount m N j
      (forcedTailColumnClass m N j))
    (_*_ m
      (forcedTailClassIncidenceEncodingFiberConstant m
        (forcedTailColumnClass m N j))
      (forcedTailClassMultiplicityBoundFormula m N
        (forcedTailColumnClass m N j)))
forcedTailColumnClassMultiplicityFromEncodingTheorem m N j =
  forcedTailClassEncodingCountBoundTheorem m N j
    (forcedTailColumnClass m N j)

forcedTailClassMultiplicityFormulaControlsBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailClassMultiplicityBoundFormula m N
      (forcedTailColumnClass m N j))
    (forcedTailColumnClassMultiplicityBound m N
      (forcedTailColumnClass m N j))
forcedTailClassMultiplicityFormulaControlsBoundTheorem m =
  forcedTailClassMultiplicityFormulaControlsBound m

forcedTailColumnMagnitudeProfileTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailColumnMagnitudeProfile m N j)
    (forcedTailColumnMagnitudeBound m N)
forcedTailColumnMagnitudeProfileTheorem m =
  forcedTailColumnMagnitudeProfileLemma m

forcedTailMagnitudeKernelUpperBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (τ : ForcedTailIncidence m) ->
  _≤_ m
    (forcedTailMagnitudeAt m N τ)
    (forcedTailMagnitudeEnvelope m N τ)
forcedTailMagnitudeKernelUpperBoundTheorem m =
  forcedTailMagnitudeKernelUpperBound m

forcedTailMagnitudeEnvelopeFactorizationTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (τ : ForcedTailIncidence m) ->
  _≤_ m
    (forcedTailMagnitudeEnvelope m N τ)
    (_*_ m
      (forcedTailMagnitudeNormalizationFactor m N τ)
      (_*_ m
        (forcedTailMagnitudeCoefficientFactor m N τ)
        (forcedTailMagnitudeProjectionFactor m N τ)))
forcedTailMagnitudeEnvelopeFactorizationTheorem m =
  forcedTailMagnitudeEnvelopeFactorization m

forcedTailColumnClassMagnitudeTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailColumnMagnitudeProfile m N j)
    (forcedTailClassMagnitudeBoundFormula m N
      (forcedTailColumnClass m N j))
forcedTailColumnClassMagnitudeTheorem m =
  forcedTailColumnClassMagnitudeLemma m

forcedTailMagnitudeEnvelopeClassBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (τ : ForcedTailIncidence m) ->
  forcedTailClassIncidenceFamily m N j
    (forcedTailColumnClass m N j) τ ->
  _≤_ m
    (forcedTailMagnitudeEnvelope m N τ)
    (forcedTailClassMagnitudeBoundFormula m N
      (forcedTailColumnClass m N j))
forcedTailMagnitudeEnvelopeClassBoundTheorem m =
  forcedTailMagnitudeEnvelopeClassBound m

forcedTailMagnitudeNormalizationClassBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (τ : ForcedTailIncidence m) ->
  forcedTailClassIncidenceFamily m N j
    (forcedTailColumnClass m N j) τ ->
  _≤_ m
    (forcedTailMagnitudeNormalizationFactor m N τ)
    (forcedTailClassNormalizationBoundFormula m N
      (forcedTailColumnClass m N j))
forcedTailMagnitudeNormalizationClassBoundTheorem m =
  forcedTailMagnitudeNormalizationClassBound m

forcedTailMagnitudeCoefficientClassBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (τ : ForcedTailIncidence m) ->
  forcedTailClassIncidenceFamily m N j
    (forcedTailColumnClass m N j) τ ->
  _≤_ m
    (forcedTailMagnitudeCoefficientFactor m N τ)
    (forcedTailClassCoefficientBoundFormula m N
      (forcedTailColumnClass m N j))
forcedTailMagnitudeCoefficientClassBoundTheorem m =
  forcedTailMagnitudeCoefficientClassBound m

forcedTailMagnitudeProjectionClassBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (τ : ForcedTailIncidence m) ->
  forcedTailClassIncidenceFamily m N j
    (forcedTailColumnClass m N j) τ ->
  _≤_ m
    (forcedTailMagnitudeProjectionFactor m N τ)
    (forcedTailClassProjectionBoundFormula m N
      (forcedTailColumnClass m N j))
forcedTailMagnitudeProjectionClassBoundTheorem m =
  forcedTailMagnitudeProjectionClassBound m

forcedTailClassEnvelopeProductControlsMagnitudeFormulaTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (_*_ m
      (forcedTailClassNormalizationBoundFormula m N
        (forcedTailColumnClass m N j))
      (_*_ m
        (forcedTailClassCoefficientBoundFormula m N
          (forcedTailColumnClass m N j))
        (forcedTailClassProjectionBoundFormula m N
          (forcedTailColumnClass m N j))))
    (forcedTailClassMagnitudeBoundFormula m N
      (forcedTailColumnClass m N j))
forcedTailClassEnvelopeProductControlsMagnitudeFormulaTheorem m =
  forcedTailClassEnvelopeProductControlsMagnitudeFormula m

forcedTailColumnClassIncidenceMagnitudeTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  (τ : ForcedTailIncidence m) ->
  forcedTailClassIncidenceFamily m N j
    (forcedTailColumnClass m N j) τ ->
  _≤_ m
    (forcedTailMagnitudeAt m N τ)
    (forcedTailClassMagnitudeBoundFormula m N
      (forcedTailColumnClass m N j))
forcedTailColumnClassIncidenceMagnitudeTheorem m N j τ τ∈class =
  ≤-trans m
    (forcedTailMagnitudeKernelUpperBound m N τ)
    (forcedTailMagnitudeEnvelopeClassBound m N j τ τ∈class)

forcedTailClassMagnitudeFormulaControlsBoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailClassMagnitudeBoundFormula m N
      (forcedTailColumnClass m N j))
    (forcedTailColumnClassMagnitudeBound m N
      (forcedTailColumnClass m N j))
forcedTailClassMagnitudeFormulaControlsBoundTheorem m =
  forcedTailClassMagnitudeFormulaControlsBound m

forcedTailColumnProfileProductTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (_*_ m
      (forcedTailColumnMultiplicityProfile m N j)
      (forcedTailColumnMagnitudeProfile m N j))
    (forcedTailColumnProfileTarget m N j)
forcedTailColumnProfileProductTheorem m =
  forcedTailColumnProfileProductLemma m

forcedTailColumnClassProductTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (_*_ m
      (forcedTailClassMultiplicityBoundFormula m N
        (forcedTailColumnClass m N j))
      (forcedTailClassMagnitudeBoundFormula m N
        (forcedTailColumnClass m N j)))
    (forcedTailClassProductFormulaTarget m N
      (forcedTailColumnClass m N j))
forcedTailColumnClassProductTheorem m =
  forcedTailColumnClassProductLemma m

forcedTailClassProductFormulaN2BoundTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (_*_ m
      (forcedTailN2Scale m N)
      (_*_ m
        (forcedTailClassMultiplicityBoundFormula m N
          (forcedTailColumnClass m N j))
        (forcedTailClassMagnitudeBoundFormula m N
          (forcedTailColumnClass m N j))))
    (forcedTailColumnClassProductN2Constant m
      (forcedTailColumnClass m N j))
forcedTailClassProductFormulaN2BoundTheorem m =
  forcedTailClassProductFormulaN2Bound m

forcedTailClassProductFormulaControlsTargetTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailClassProductFormulaTarget m N
      (forcedTailColumnClass m N j))
    (forcedTailColumnClassProductTarget m N
      (forcedTailColumnClass m N j))
forcedTailClassProductFormulaControlsTargetTheorem m =
  forcedTailClassProductFormulaControlsTarget m

forcedTailColumnClassTargetProductTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (_*_ m
      (forcedTailColumnClassMultiplicityBound m N
        (forcedTailColumnClass m N j))
      (forcedTailColumnClassMagnitudeBound m N
        (forcedTailColumnClass m N j)))
    (forcedTailColumnClassProductTarget m N
      (forcedTailColumnClass m N j))
forcedTailColumnClassTargetProductTheorem m =
  forcedTailColumnClassTargetProductLemma m

forcedTailClassToColumnMultiplicityLiftTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailColumnMultiplicityProfile m N j)
    (forcedTailColumnClassMultiplicityBound m N
      (forcedTailColumnClass m N j))
forcedTailClassToColumnMultiplicityLiftTheorem m =
  forcedTailClassToColumnMultiplicityLift m

forcedTailClassToColumnMagnitudeLiftTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailColumnMagnitudeProfile m N j)
    (forcedTailColumnClassMagnitudeBound m N
      (forcedTailColumnClass m N j))
forcedTailClassToColumnMagnitudeLiftTheorem m =
  forcedTailClassToColumnMagnitudeLift m

forcedTailClassToColumnProductLiftTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailColumnProfileTarget m N j)
    (forcedTailColumnClassProductTarget m N
      (forcedTailColumnClass m N j))
forcedTailClassToColumnProductLiftTheorem m =
  forcedTailClassToColumnProductLift m

forcedTailColumnSumByMultiplicityMagnitudeTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  let wN = weightAt m N in
  _≤_ m
    (forcedTailColumnWeightedSum m N j wN)
    (_*_ m
      (forcedTailColumnMultiplicityProfile m N j)
      (forcedTailColumnMagnitudeProfile m N j))
forcedTailColumnSumByMultiplicityMagnitudeTheorem m =
  forcedTailColumnSumByMultiplicityMagnitude m

forcedTailColumnToShellN2LiftTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  (j : Column m) ->
  _≤_ m
    (forcedTailColumnClassProductTarget m N
      (forcedTailColumnClass m N j))
    (forcedTailColumnN2Target m N)
forcedTailColumnToShellN2LiftTheorem m =
  forcedTailColumnToShellN2Lift m

forcedTailCountingMagnitudeProductTheorem :
  ∀ {ℓS ℓE ℓW ℓV ℓR}
  (m : NSTriadKNForcedTailCountingMagnitudeTheoremModel
         {ℓS} {ℓE} {ℓW} {ℓV} {ℓR}) ->
  (N : Shell (decompositionModel m)) ->
  let wN = weightAt m N in
  _≤_ m
    (_*_ m
      (forcedTailRowFunctional m N wN)
      (forcedTailColumnFunctional m N wN))
    (forcedTailProductTarget m N)
forcedTailCountingMagnitudeProductTheorem m =
  forcedTailProductConclusion m
