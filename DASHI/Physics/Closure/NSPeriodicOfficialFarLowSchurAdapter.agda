module DASHI.Physics.Closure.NSPeriodicOfficialFarLowSchurAdapter where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicFourierAnalyticAuthorityBoundary as Authority
import DASHI.Physics.Closure.NSPeriodicFourierAuthorityAdapters as Selected
import DASHI.Physics.Closure.NSPeriodicOfficialHarmonicAuthorityCompletion as Base
import DASHI.Physics.Closure.NSPeriodicFarLowOfficialSchurCompletion as Low

------------------------------------------------------------------------
-- Factorized far-low adapter.
--
-- The generic published harmonic authority supplies the commutator and
-- multiplier estimates.  This adapter requires the actual official weighted row
-- and column constants and an exact proof that their product is the full Schur
-- constant.  It returns both the far-low estimate package and the coherence
-- witness required by Wall I.
------------------------------------------------------------------------

record FactorizedFarLowAuthorityInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    {Index Shell Time State : Set i}
    (S : Selected.SelectedPeriodicHarmonicAuthority
      A Index Shell Time State) : Set (lsuc i) where
  field
    base : Base.FarLowAuthorityCompletionInputs A S

    weightedRowSchur weightedColumnSchur :
      Index → Time → Scalar A

    fullOfficialSchurMeaning : ∀ q τ →
      Base.fullOfficialSchur base q τ ≡
      _∗_ A
        (weightedRowSchur q τ)
        (weightedColumnSchur q τ)

open FactorizedFarLowAuthorityInputs public

factorizedFarLowFromSelectedAuthority :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : Selected.SelectedPeriodicHarmonicAuthority
    A Index Shell Time State) →
  FactorizedFarLowAuthorityInputs A S →
  Low.PeriodicFarLowOfficialSchurInputs A Index Time State
factorizedFarLowFromSelectedAuthority S I = record
  { Admissible = Base.selectedStateOnlyAdmissible S
  ; farLowOperator = λ q τ u → Base.farLowOperator (base I) q τ
  ; commutatorOperator = λ q τ u →
      Authority.farLowCommutator
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; multiplierMajorant = λ q τ u →
      Authority.meanValueMajorant
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; weightedRowSchur = λ q τ u → weightedRowSchur I q τ
  ; weightedColumnSchur = λ q τ u → weightedColumnSchur I q τ
  ; fullOfficialSchur = λ q τ u →
      Base.fullOfficialSchur (base I) q τ
  ; radiusEightOfficialBudget = λ q τ u →
      Base.radiusEightOfficialBudget (base I) q τ
  ; DivergenceFreeCancellation = λ q τ u →
      Base.DivergenceFreeCancellation (base I)
  ; BothLinearizedPlacementsIncluded = λ q τ u →
      Base.BothLinearizedPlacementsIncluded (base I)
  ; BiotSavartAndLerayMatched = λ q τ u →
      Base.BiotSavartAndLerayMatched (base I)
  ; WeightedSchurFactorization = λ q τ u →
      Base.WeightedSchurFactorization (base I)
  ; divergenceFreeCancellation = λ q τ u admissible →
      Base.divergenceFreeCancellation (base I)
  ; bothLinearizedPlacementsIncluded = λ q τ u admissible →
      Base.bothLinearizedPlacementsIncluded (base I)
  ; biotSavartAndLerayMatched = λ q τ u admissible →
      Base.biotSavartAndLerayMatched (base I)
  ; weightedSchurFactorization = λ q τ u admissible →
      Base.weightedSchurFactorization (base I)
  ; farLowRewrittenAsCommutator = λ q τ u admissible →
      Base.farLowRewrittenAsCommutator (base I) q τ
  ; smoothMultiplierDifferenceBound = λ q τ u admissible →
      Base.farLowCommutatorToMeanValue S q τ
  ; officialWeightedSchurBound = λ q τ u admissible →
      Base.officialWeightedSchurBound (base I) q τ
  ; radiusEightFullConstantFitsBudget = λ q τ u admissible →
      Base.radiusEightFullConstantFitsBudget (base I) q τ
  ; CutoffUniform = Base.CutoffUniform (base I)
  ; cutoffUniform = Base.cutoffUniform (base I)
  }

factorizedFarLowSchurCoherence :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : Selected.SelectedPeriodicHarmonicAuthority
    A Index Shell Time State) →
  (I : FactorizedFarLowAuthorityInputs A S) →
  Low.PeriodicFarLowSchurFactorCoherence
    (factorizedFarLowFromSelectedAuthority S I)
factorizedFarLowSchurCoherence S I = record
  { fullOfficialSchurMeaning = λ q τ u →
      fullOfficialSchurMeaning I q τ
  }

factorizedFarLowRadiusEightEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : Selected.SelectedPeriodicHarmonicAuthority
    A Index Shell Time State) →
  (I : FactorizedFarLowAuthorityInputs A S) →
  ∀ q τ u →
  Low.Admissible
    (factorizedFarLowFromSelectedAuthority S I) q τ u →
  _≤_ A
    (Low.farLowOperator
      (factorizedFarLowFromSelectedAuthority S I) q τ u)
    (Low.radiusEightOfficialBudget
      (factorizedFarLowFromSelectedAuthority S I) q τ u)
factorizedFarLowRadiusEightEstimate S I =
  Low.periodicFarLowOfficialRadiusEightEstimate
    (factorizedFarLowFromSelectedAuthority S I)
