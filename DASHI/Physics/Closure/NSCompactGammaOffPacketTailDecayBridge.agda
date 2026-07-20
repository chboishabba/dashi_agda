module DASHI.Physics.Closure.NSCompactGammaOffPacketTailDecayBridge where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaOffPacketSchurSplit

------------------------------------------------------------------------
-- Radius-indexed off-packet splits
------------------------------------------------------------------------

record RadiusIndexedOffPacketSplit
    {r : Level}
    (Radius : Set r)
    (A : AbsorptionArithmetic) : Set (lsuc r) where
  field
    splitAt : Radius → OffPacketSchurSplitInputs A

open RadiusIndexedOffPacketSplit public

------------------------------------------------------------------------
-- Multiplicative arithmetic used by quantitative tail estimates.
--
-- The base absorption arithmetic deliberately knows only addition and order.
-- A bound of the form epsilon(R) E_K(u) ||h||_X additionally needs a
-- monotone scalar product.  Keeping this extension separate preserves every
-- existing additive bridge.
------------------------------------------------------------------------

record TailProductArithmetic
    (A : AbsorptionArithmetic) : Set₁ where
  field
    _·_ : Scalar A → Scalar A → Scalar A

    multiplicationMonotoneLeft :
      {a b c : Scalar A} →
      _≤_ A a b →
      _≤_ A (_·_ c a) (_·_ c b)

    multiplicationMonotoneRight :
      {a b c : Scalar A} →
      _≤_ A a b →
      _≤_ A (_·_ a c) (_·_ b c)

open TailProductArithmetic public

------------------------------------------------------------------------
-- Exact analytic leaves for the two far-frequency regions.
--
-- These records do not replace the Fourier estimates.  They state their
-- concrete proof obligations without permitting naive absolute-value counting
-- to masquerade as the far-low argument.
------------------------------------------------------------------------

record FarShellFrequencySplit
    (A : AbsorptionArithmetic) : Set₁ where
  field
    fullFarTail : Scalar A
    farHighTail : Scalar A
    farLowTail  : Scalar A

    fullFarTailBelowHighPlusLow :
      _≤_ A fullFarTail (_+_ A farHighTail farLowTail)

open FarShellFrequencySplit public

record HighFrequencyParaproductEstimate
    (A : AbsorptionArithmetic) : Set₁ where
  field
    highHighResponse : Scalar A
    highLowResponse  : Scalar A
    highHighBudget   : Scalar A
    highLowBudget    : Scalar A
    commonHighDecayBudget : Scalar A

    farHighResponse : Scalar A

    farHighBelowHighHighPlusHighLow :
      _≤_ A farHighResponse
        (_+_ A highHighResponse highLowResponse)

    highHighParaproductDecay :
      _≤_ A highHighResponse highHighBudget

    highLowParaproductDecay :
      _≤_ A highLowResponse highLowBudget

    highBudgetsBelowCommonDecay :
      _≤_ A
        (_+_ A highHighBudget highLowBudget)
        commonHighDecayBudget

open HighFrequencyParaproductEstimate public

highFrequencyParaproductsDecay :
  (A : AbsorptionArithmetic) →
  (H : HighFrequencyParaproductEstimate A) →
  _≤_ A (farHighResponse H) (commonHighDecayBudget H)
highFrequencyParaproductsDecay A H =
  ≤-trans A
    (farHighBelowHighHighPlusHighLow H)
    (≤-trans A
      (additionMonotoneRight A (highHighParaproductDecay H))
      (≤-trans A
        (additionMonotoneLeft A (highLowParaproductDecay H))
        (highBudgetsBelowCommonDecay H)))

record LowHighCommutatorCancellation
    (A : AbsorptionArithmetic) : Set₁ where
  field
    farLowResponse : Scalar A

    biotSavartGain : Scalar A
    shellGeometryGain : Scalar A
    targetFrequencyCancellationGain : Scalar A

    cancelledLowHighResponse : Scalar A
    commonLowDecayBudget : Scalar A

    -- This is the decisive analytic leaf.  It must be proved from the
    -- divergence-free identity or an equivalent commutator formula before
    -- absolute values are taken.
    lowHighCommutatorCancellation :
      _≤_ A farLowResponse cancelledLowHighResponse

    biotSavartShellCancellationAssembles :
      _≤_ A cancelledLowHighResponse
        (_+_ A
          biotSavartGain
          (_+_ A shellGeometryGain targetFrequencyCancellationGain))

    assembledLowHighGainDecays :
      _≤_ A
        (_+_ A
          biotSavartGain
          (_+_ A shellGeometryGain targetFrequencyCancellationGain))
        commonLowDecayBudget

open LowHighCommutatorCancellation public

lowHighCancellationDecays :
  (A : AbsorptionArithmetic) →
  (L : LowHighCommutatorCancellation A) →
  _≤_ A (farLowResponse L) (commonLowDecayBudget L)
lowHighCancellationDecays A L =
  ≤-trans A
    (lowHighCommutatorCancellation L)
    (≤-trans A
      (biotSavartShellCancellationAssembles L)
      (assembledLowHighGainDecays L))

------------------------------------------------------------------------
-- Discrete Z^3 shell bookkeeping and tangent-norm domination.
------------------------------------------------------------------------

record DyadicConvolutionLemmaZ3
    (A : AbsorptionArithmetic) : Set₁ where
  field
    discreteDyadicConvolution : Scalar A
    dyadicVolumeMajorant : Scalar A
    cutoffUniformConvolutionBudget : Scalar A

    discreteSumBelowDyadicVolume :
      _≤_ A discreteDyadicConvolution dyadicVolumeMajorant

    dyadicVolumeBelowUniformBudget :
      _≤_ A dyadicVolumeMajorant cutoffUniformConvolutionBudget

open DyadicConvolutionLemmaZ3 public

dyadicConvolutionUniformInCutoff :
  (A : AbsorptionArithmetic) →
  (D : DyadicConvolutionLemmaZ3 A) →
  _≤_ A
    (discreteDyadicConvolution D)
    (cutoffUniformConvolutionBudget D)
dyadicConvolutionUniformInCutoff A D =
  ≤-trans A
    (discreteSumBelowDyadicVolume D)
    (dyadicVolumeBelowUniformBudget D)

record TailNormDomination
    (A : AbsorptionArithmetic) : Set₁ where
  field
    measuredTailNorm : Scalar A
    chosenTangentNorm : Scalar A

    tailNormBelowChosenTangentNorm :
      _≤_ A measuredTailNorm chosenTangentNorm

open TailNormDomination public

------------------------------------------------------------------------
-- Quantitative geometric decay.
--
-- `epsilon radius` is the common coefficient after high and low estimates.
-- `dyadicCoefficient radius` is the concrete C 2^(-alpha R) evaluator.  The
-- equality keeps the theorem quantitative while leaving the scalar model free
-- to instantiate exact rationals, constructive reals, or an ordered field.
------------------------------------------------------------------------

record DyadicGeometricRate
    {r : Level}
    {Radius : Set r}
    (A : AbsorptionArithmetic) : Set (lsuc r) where
  field
    constantC : Scalar A
    exponentAlpha : Scalar A

    dyadicCoefficient : Radius → Scalar A
    epsilon : Radius → Scalar A

    epsilonIsC2^-alphaR :
      (radius : Radius) →
      epsilon radius ≡ dyadicCoefficient radius

    AdmissibleCoefficientBudget : Scalar A → Set

    geometricEventuallyBelow :
      (budget : Scalar A) →
      AdmissibleCoefficientBudget budget →
      Σ Radius (λ radius → _≤_ A (epsilon radius) budget)

open DyadicGeometricRate public

record UniformAnalyticTailDecay
    {r : Level}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (M : TailProductArithmetic A)
    (F : RadiusIndexedOffPacketSplit Radius A) : Set (lsuc r) where
  field
    rate : DyadicGeometricRate {Radius = Radius} A

    shellEnergy : Scalar A
    tangentNorm : Scalar A

    quantitativeTailBound :
      (radius : Radius) →
      _≤_ A
        (farShellTail (splitAt F radius))
        (_·_ M
          (epsilon rate radius)
          (_·_ M shellEnergy tangentNorm))

open UniformAnalyticTailDecay public

------------------------------------------------------------------------
-- Assembly theorem from the high/high, high/low, and cancelled low/high lanes.
------------------------------------------------------------------------

record UniformFourierTailAssembly
    {r : Level}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (M : TailProductArithmetic A)
    (F : RadiusIndexedOffPacketSplit Radius A)
    (Q : UniformAnalyticTailDecay A M F) : Set (lsuc r) where
  field
    frequencySplit : Radius → FarShellFrequencySplit A
    highEstimate : Radius → HighFrequencyParaproductEstimate A
    lowCancellation : Radius → LowHighCommutatorCancellation A
    latticeConvolution : Radius → DyadicConvolutionLemmaZ3 A
    normDomination : Radius → TailNormDomination A

    splitMatchesMeasuredTail :
      (radius : Radius) →
      fullFarTail (frequencySplit radius) ≡
      farShellTail (splitAt F radius)

    splitHighMatchesEstimate :
      (radius : Radius) →
      farHighTail (frequencySplit radius) ≡
      farHighResponse (highEstimate radius)

    splitLowMatchesCancellation :
      (radius : Radius) →
      farLowTail (frequencySplit radius) ≡
      farLowResponse (lowCancellation radius)

    -- Common dyadic endpoint after inserting the Z^3 convolution comparison
    -- and tail-norm domination into both paraproduct bounds.
    highPlusLowBelowGeometricBudget :
      (radius : Radius) →
      _≤_ A
        (_+_ A
          (commonHighDecayBudget (highEstimate radius))
          (commonLowDecayBudget (lowCancellation radius)))
        (_·_ M
          (epsilon (rate Q) radius)
          (_·_ M (shellEnergy Q) (tangentNorm Q)))

open UniformFourierTailAssembly public

assembledFourierTailDecay :
  ∀ {r}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (M : TailProductArithmetic A)
    (F : RadiusIndexedOffPacketSplit Radius A)
    (Q : UniformAnalyticTailDecay A M F) →
  (S : UniformFourierTailAssembly A M F Q) →
  (radius : Radius) →
  _≤_ A
    (farShellTail (splitAt F radius))
    (_·_ M
      (epsilon (rate Q) radius)
      (_·_ M (shellEnergy Q) (tangentNorm Q)))
assembledFourierTailDecay A M F Q S radius =
  ≤-trans A tailToSplitSum
    (≤-trans A splitSumToDecayBudgets
      (highPlusLowBelowGeometricBudget S radius))
  where
  tailToSplitSum :
    _≤_ A
      (farShellTail (splitAt F radius))
      (_+_ A
        (farHighTail (frequencySplit S radius))
        (farLowTail (frequencySplit S radius)))
  tailToSplitSum rewrite splitMatchesMeasuredTail S radius =
    fullFarTailBelowHighPlusLow (frequencySplit S radius)

  splitSumToDecayBudgets :
    _≤_ A
      (_+_ A
        (farHighTail (frequencySplit S radius))
        (farLowTail (frequencySplit S radius)))
      (_+_ A
        (commonHighDecayBudget (highEstimate S radius))
        (commonLowDecayBudget (lowCancellation S radius)))
  splitSumToDecayBudgets
    rewrite splitHighMatchesEstimate S radius
          | splitLowMatchesCancellation S radius =
    ≤-trans A
      (additionMonotoneRight A
        (highFrequencyParaproductsDecay A (highEstimate S radius)))
      (additionMonotoneLeft A
        (lowHighCancellationDecays A (lowCancellation S radius)))

------------------------------------------------------------------------
-- Order-theoretic consequence used by tail absorption.
------------------------------------------------------------------------

record OrderVanishingTail
    {r : Level}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (F : RadiusIndexedOffPacketSplit Radius A) : Set (lsuc r) where
  field
    AdmissibleTailBudget : Scalar A → Set

    tailEventuallyBelow :
      (budget : Scalar A) →
      AdmissibleTailBudget budget →
      Σ Radius
        (λ radius →
          _≤_ A
            (farShellTail (splitAt F radius))
            budget)

open OrderVanishingTail public

record QuantitativeTailBudgetWitness
    {r : Level}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (M : TailProductArithmetic A)
    (F : RadiusIndexedOffPacketSplit Radius A)
    (Q : UniformAnalyticTailDecay A M F)
    (tailBudget : Scalar A) : Set (lsuc r) where
  field
    coefficientBudget : Scalar A

    coefficientBudgetAdmissible :
      AdmissibleCoefficientBudget (rate Q) coefficientBudget

    scaledCoefficientBelowTailBudget :
      _≤_ A
        (_·_ M
          coefficientBudget
          (_·_ M (shellEnergy Q) (tangentNorm Q)))
        tailBudget

open QuantitativeTailBudgetWitness public

quantitativeDecayToOrderVanishingTail :
  ∀ {r}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (M : TailProductArithmetic A)
    (F : RadiusIndexedOffPacketSplit Radius A) →
  (Q : UniformAnalyticTailDecay A M F) →
  OrderVanishingTail A F
quantitativeDecayToOrderVanishingTail A M F Q =
  record
    { AdmissibleTailBudget = QuantitativeTailBudgetWitness A M F Q
    ; tailEventuallyBelow = select
    }
  where
  select :
    (budget : Scalar A) →
    QuantitativeTailBudgetWitness A M F Q budget →
    Σ Radius
      (λ radius →
        _≤_ A
          (farShellTail (splitAt F radius))
          budget)
  select budget W
    with geometricEventuallyBelow (rate Q)
      (coefficientBudget W)
      (coefficientBudgetAdmissible W)
  ... | radius , coefficientBound =
    radius ,
      ≤-trans A
        (quantitativeTailBound Q radius)
        (≤-trans A
          (multiplicationMonotoneRight M coefficientBound)
          (scaledCoefficientBelowTailBudget W))

------------------------------------------------------------------------
-- Radius selection and absorption, unchanged downstream.
------------------------------------------------------------------------

record TailAbsorptionTarget
    {r : Level}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (F : RadiusIndexedOffPacketSplit Radius A)
    (V : OrderVanishingTail A F) : Set (lsuc r) where
  field
    targetTailBudget : Scalar A
    targetFullOffPacketBudget : Scalar A

    targetBudgetAdmissible :
      AdmissibleTailBudget V targetTailBudget

    targetSchurPlusTailBelowFull :
      (radius : Radius) →
      _≤_ A
        (_+_ A
          (schurWeightedBudget (splitAt F radius))
          targetTailBudget)
        targetFullOffPacketBudget

open TailAbsorptionTarget public

selectRadiusAndAssembleTailAbsorption :
  ∀ {r}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (F : RadiusIndexedOffPacketSplit Radius A)
    (V : OrderVanishingTail A F) →
  (T : TailAbsorptionTarget A F V) →
  Σ Radius
    (λ radius → OffPacketTailAbsorptionInputs A)
selectRadiusAndAssembleTailAbsorption A F V T
  with tailEventuallyBelow V
    (targetTailBudget T)
    (targetBudgetAdmissible T)
... | radius , tailBound =
  radius , record
    { tailSplitInputs = splitAt F radius
    ; absorbedTailBudget = targetTailBudget T
    ; fullOffPacketBudget = targetFullOffPacketBudget T
    ; farTailBelowAbsorbedBudget = tailBound
    ; schurPlusAbsorbedTailBelowFullBudget =
        targetSchurPlusTailBelowFull T radius
    }

selectedRadiusBoundsOffPacketResponse :
  ∀ {r}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (F : RadiusIndexedOffPacketSplit Radius A)
    (V : OrderVanishingTail A F)
    (T : TailAbsorptionTarget A F V) →
  Σ Radius
    (λ radius →
      _≤_ A
        (offPacketResponse (splitAt F radius))
        (targetFullOffPacketBudget T))
selectedRadiusBoundsOffPacketResponse A F V T
  with selectRadiusAndAssembleTailAbsorption A F V T
... | radius , inputs =
  radius , absorbedTailBoundsOffPacketResponse A inputs
