module DASHI.Physics.Closure.NSPeriodicOfficialHarmonicAuthorityCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicFourierAnalyticAuthorityBoundary as Authority
import DASHI.Physics.Closure.NSPeriodicFourierAuthorityAdapters as Selected
import DASHI.Physics.Closure.NSPeriodicNearTriadCutoffUniformCompletion as Near
import DASHI.Physics.Closure.NSPeriodicFarLowOfficialSchurCompletion as Low
import DASHI.Physics.Closure.NSPeriodicFarHighTailCompletion as High

------------------------------------------------------------------------
-- Carrier-exact adapters from the selected published periodic harmonic authority
-- already present in the repository.
--
-- Standard Bony, smooth-multiplier and Sobolev-placement estimates are consumed
-- here.  The nonstandard compact-Gamma factor interpretations, official Schur
-- norm, complete R=8 budgets and geometric payment remain explicit inputs.
------------------------------------------------------------------------

selectedStateOnlyAdmissible :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  Selected.SelectedPeriodicHarmonicAuthority A Index Shell Time State →
  Index → Time → State → Set i
selectedStateOnlyAdmissible S q τ u =
  u ≡ Selected.selectedState S q τ

------------------------------------------------------------------------
-- Near triads.
------------------------------------------------------------------------

record NearTriadAuthorityCompletionInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    {Index Shell Time State : Set i}
    (S : Selected.SelectedPeriodicHarmonicAuthority
      A Index Shell Time State) : Set (lsuc i) where
  field
    nearTotal : Index → Time → Scalar A

    exactNearTriadDecomposition : ∀ q τ →
      nearTotal q τ ≡
      _+_ A
        (_+_ A
          (Authority.nearLowHigh
            (Selected.authority S) q τ (Selected.selectedState S q τ))
          (Authority.nearHighLow
            (Selected.authority S) q τ (Selected.selectedState S q τ)))
        (Authority.nearHighHigh
          (Selected.authority S) q τ (Selected.selectedState S q τ))

    lowHighDissipationPayment lowHighResidualPayment :
      Index → Time → Scalar A
    highLowDissipationPayment highLowResidualPayment :
      Index → Time → Scalar A
    highHighDissipationPayment highHighResidualPayment :
      Index → Time → Scalar A

    lowHighFactorInterpretation : ∀ q τ →
      Authority.nearLowHighProduct
        (Selected.authority S) q τ (Selected.selectedState S q τ)
      ≡ _+_ A
          (lowHighDissipationPayment q τ)
          (lowHighResidualPayment q τ)

    highLowFactorInterpretation : ∀ q τ →
      Authority.nearHighLowProduct
        (Selected.authority S) q τ (Selected.selectedState S q τ)
      ≡ _+_ A
          (highLowDissipationPayment q τ)
          (highLowResidualPayment q τ)

    highHighFactorInterpretation : ∀ q τ →
      Authority.nearHighHighProduct
        (Selected.authority S) q τ (Selected.selectedState S q τ)
      ≡ _+_ A
          (highHighDissipationPayment q τ)
          (highHighResidualPayment q τ)

    officialNearBudget : Index → Time → Scalar A

    commonYoungPaymentBudget : ∀ q τ →
      _≤_ A
        (_+_ A
          (_+_ A
            (Authority.nearLowHighProduct
              (Selected.authority S) q τ (Selected.selectedState S q τ))
            (Authority.nearHighLowProduct
              (Selected.authority S) q τ (Selected.selectedState S q τ)))
          (Authority.nearHighHighProduct
            (Selected.authority S) q τ (Selected.selectedState S q τ)))
        (officialNearBudget q τ)

    CutoffUniform : Set i
    cutoffUniform : CutoffUniform

open NearTriadAuthorityCompletionInputs public

nearTriadFromSelectedAuthority :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : Selected.SelectedPeriodicHarmonicAuthority
    A Index Shell Time State) →
  NearTriadAuthorityCompletionInputs A S →
  Near.PeriodicNearTriadUniformInputs A Index Time State
nearTriadFromSelectedAuthority S I = record
  { Admissible = selectedStateOnlyAdmissible S
  ; nearTotal = λ q τ u → nearTotal I q τ
  ; nearLowHigh = λ q τ u →
      Authority.nearLowHigh
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; nearHighLow = λ q τ u →
      Authority.nearHighLow
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; nearHighHigh = λ q τ u →
      Authority.nearHighHigh
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; lowHighUpper = λ q τ u →
      Authority.nearLowHighProduct
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; highLowUpper = λ q τ u →
      Authority.nearHighLowProduct
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; highHighUpper = λ q τ u →
      Authority.nearHighHighProduct
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; officialNearBudget = λ q τ u → officialNearBudget I q τ
  ; lowHighDissipationPayment = λ q τ u → lowHighDissipationPayment I q τ
  ; lowHighResidualPayment = λ q τ u → lowHighResidualPayment I q τ
  ; highLowDissipationPayment = λ q τ u → highLowDissipationPayment I q τ
  ; highLowResidualPayment = λ q τ u → highLowResidualPayment I q τ
  ; highHighDissipationPayment = λ q τ u → highHighDissipationPayment I q τ
  ; highHighResidualPayment = λ q τ u → highHighResidualPayment I q τ
  ; exactNearTriadDecomposition = λ q τ u →
      exactNearTriadDecomposition I q τ
  ; lowHighProductEstimate = λ q τ u admissible →
      Selected.selectedBonyLowHighEstimate S q τ
  ; highLowProductEstimate = λ q τ u admissible →
      Selected.selectedBonyHighLowEstimate S q τ
  ; highHighProductEstimate = λ q τ u admissible →
      Selected.selectedBonyHighHighEstimate S q τ
  ; lowHighFactorInterpretation = λ q τ u →
      lowHighFactorInterpretation I q τ
  ; highLowFactorInterpretation = λ q τ u →
      highLowFactorInterpretation I q τ
  ; highHighFactorInterpretation = λ q τ u →
      highHighFactorInterpretation I q τ
  ; commonYoungPaymentBudget = λ q τ u →
      commonYoungPaymentBudget I q τ
  ; CutoffUniform = CutoffUniform I
  ; cutoffUniform = cutoffUniform I
  }

------------------------------------------------------------------------
-- Far-low commutator plus official Schur normalization.
------------------------------------------------------------------------

record FarLowAuthorityCompletionInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    {Index Shell Time State : Set i}
    (S : Selected.SelectedPeriodicHarmonicAuthority
      A Index Shell Time State) : Set (lsuc i) where
  field
    farLowOperator fullOfficialSchur radiusEightOfficialBudget :
      Index → Time → Scalar A

    DivergenceFreeCancellation BothLinearizedPlacementsIncluded
      BiotSavartAndLerayMatched WeightedSchurFactorization : Set i

    divergenceFreeCancellation : DivergenceFreeCancellation
    bothLinearizedPlacementsIncluded : BothLinearizedPlacementsIncluded
    biotSavartAndLerayMatched : BiotSavartAndLerayMatched
    weightedSchurFactorization : WeightedSchurFactorization

    farLowRewrittenAsCommutator : ∀ q τ →
      _≤_ A (farLowOperator q τ)
        (Authority.farLowCommutator
          (Selected.authority S) q τ (Selected.selectedState S q τ))

    officialWeightedSchurBound : ∀ q τ →
      _≤_ A
        (Authority.meanValueMajorant
          (Selected.authority S) q τ (Selected.selectedState S q τ))
        (fullOfficialSchur q τ)

    radiusEightFullConstantFitsBudget : ∀ q τ →
      _≤_ A (fullOfficialSchur q τ) (radiusEightOfficialBudget q τ)

    CutoffUniform : Set i
    cutoffUniform : CutoffUniform

open FarLowAuthorityCompletionInputs public

farLowCommutatorToMeanValue :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : Selected.SelectedPeriodicHarmonicAuthority
    A Index Shell Time State) →
  ∀ q τ →
  _≤_ A
    (Authority.farLowCommutator
      (Selected.authority S) q τ (Selected.selectedState S q τ))
    (Authority.meanValueMajorant
      (Selected.authority S) q τ (Selected.selectedState S q τ))
farLowCommutatorToMeanValue {A = A} S q τ =
  ≤-trans A
    (Selected.selectedFarLowCommutatorEstimate S q τ)
    (Selected.selectedMultiplierMeanValueEstimate S q τ)

farLowFromSelectedAuthority :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : Selected.SelectedPeriodicHarmonicAuthority
    A Index Shell Time State) →
  FarLowAuthorityCompletionInputs A S →
  Low.PeriodicFarLowOfficialSchurInputs A Index Time State
farLowFromSelectedAuthority S I = record
  { Admissible = selectedStateOnlyAdmissible S
  ; farLowOperator = λ q τ u → farLowOperator I q τ
  ; commutatorOperator = λ q τ u →
      Authority.farLowCommutator
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; multiplierMajorant = λ q τ u →
      Authority.meanValueMajorant
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; weightedRowSchur = λ q τ u → fullOfficialSchur I q τ
  ; weightedColumnSchur = λ q τ u → fullOfficialSchur I q τ
  ; fullOfficialSchur = λ q τ u → fullOfficialSchur I q τ
  ; radiusEightOfficialBudget = λ q τ u → radiusEightOfficialBudget I q τ
  ; DivergenceFreeCancellation = λ q τ u → DivergenceFreeCancellation I
  ; BothLinearizedPlacementsIncluded = λ q τ u →
      BothLinearizedPlacementsIncluded I
  ; BiotSavartAndLerayMatched = λ q τ u → BiotSavartAndLerayMatched I
  ; WeightedSchurFactorization = λ q τ u → WeightedSchurFactorization I
  ; divergenceFreeCancellation = λ q τ u admissible →
      divergenceFreeCancellation I
  ; bothLinearizedPlacementsIncluded = λ q τ u admissible →
      bothLinearizedPlacementsIncluded I
  ; biotSavartAndLerayMatched = λ q τ u admissible →
      biotSavartAndLerayMatched I
  ; weightedSchurFactorization = λ q τ u admissible →
      weightedSchurFactorization I
  ; farLowRewrittenAsCommutator = λ q τ u admissible →
      farLowRewrittenAsCommutator I q τ
  ; smoothMultiplierDifferenceBound = λ q τ u admissible →
      farLowCommutatorToMeanValue S q τ
  ; officialWeightedSchurBound = λ q τ u admissible →
      officialWeightedSchurBound I q τ
  ; radiusEightFullConstantFitsBudget = λ q τ u admissible →
      radiusEightFullConstantFitsBudget I q τ
  ; CutoffUniform = CutoffUniform I
  ; cutoffUniform = cutoffUniform I
  }

------------------------------------------------------------------------
-- Far-high two-placement Sobolev and geometric tail.
------------------------------------------------------------------------

record FarHighAuthorityCompletionInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    {Index Shell Time State : Set i}
    (S : Selected.SelectedPeriodicHarmonicAuthority
      A Index Shell Time State) : Set (lsuc i) where
  field
    farHighTotal : Index → Time → Scalar A

    exactPlacementDecomposition : ∀ q τ →
      farHighTotal q τ ≡
      _+_ A
        (Authority.farHighLeft
          (Selected.authority S) q τ (Selected.selectedState S q τ))
        (Authority.farHighRight
          (Selected.authority S) q τ (Selected.selectedState S q τ))

    hSobolevMajorant geometricTailMajorant radiusEightOfficialBudget :
      Index → Time → Scalar A

    placementSumBelowSobolev : ∀ q τ →
      _≤_ A
        (_+_ A
          (Authority.farHighSobolevMajorant
            (Selected.authority S) q τ (Selected.selectedState S q τ))
          (Authority.farHighSobolevMajorant
            (Selected.authority S) q τ (Selected.selectedState S q τ)))
        (hSobolevMajorant q τ)

    exactGeometricTailSummation : ∀ q τ →
      _≤_ A (hSobolevMajorant q τ) (geometricTailMajorant q τ)

    radiusEightFullConstantFitsBudget : ∀ q τ →
      _≤_ A (geometricTailMajorant q τ) (radiusEightOfficialBudget q τ)

    CutoffUniform : Set i
    cutoffUniform : CutoffUniform

open FarHighAuthorityCompletionInputs public

farHighFromSelectedAuthority :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : Selected.SelectedPeriodicHarmonicAuthority
    A Index Shell Time State) →
  FarHighAuthorityCompletionInputs A S →
  High.PeriodicFarHighTailInputs A Index Time State
farHighFromSelectedAuthority S I = record
  { Admissible = selectedStateOnlyAdmissible S
  ; farHighTotal = λ q τ u → farHighTotal I q τ
  ; leftPlacement = λ q τ u →
      Authority.farHighLeft
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; rightPlacement = λ q τ u →
      Authority.farHighRight
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; placementSum = λ q τ u →
      _+_ A
        (Authority.farHighSobolevMajorant
          (Selected.authority S) q τ (Selected.selectedState S q τ))
        (Authority.farHighSobolevMajorant
          (Selected.authority S) q τ (Selected.selectedState S q τ))
  ; highFiveHalvesTail = λ q τ u →
      Authority.farHighSobolevMajorant
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; hSobolevMajorant = λ q τ u → hSobolevMajorant I q τ
  ; geometricTailMajorant = λ q τ u → geometricTailMajorant I q τ
  ; radiusEightOfficialBudget = λ q τ u → radiusEightOfficialBudget I q τ
  ; exactPlacementDecomposition = λ q τ u →
      exactPlacementDecomposition I q τ
  ; leftPlacementProductEstimate = λ q τ u admissible →
      Selected.selectedFarHighLeftEstimate S q τ
  ; rightPlacementProductEstimate = λ q τ u admissible →
      Selected.selectedFarHighRightEstimate S q τ
  ; placementSumMeaning = λ q τ u → refl
  ; sobolevToHighShellTail = λ q τ u admissible →
      placementSumBelowSobolev I q τ
  ; exactGeometricTailSummation = λ q τ u admissible →
      exactGeometricTailSummation I q τ
  ; radiusEightFullConstantFitsBudget = λ q τ u admissible →
      radiusEightFullConstantFitsBudget I q τ
  ; CutoffUniform = CutoffUniform I
  ; cutoffUniform = cutoffUniform I
  }
