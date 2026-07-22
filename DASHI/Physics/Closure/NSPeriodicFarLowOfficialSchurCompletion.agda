module DASHI.Physics.Closure.NSPeriodicFarLowOfficialSchurCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Complete far-low operator surface in the official norm.
--
-- The raw smooth-multiplier gain is deliberately not the endpoint.  The owner
-- below retains the divergence-free cancellation, both linearized placements,
-- Biot--Savart, Leray, convolution multiplicity, weighted row/column Schur
-- estimates, and the final R=8 budget in one coherent theorem package.
------------------------------------------------------------------------

record PeriodicFarLowOfficialSchurInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Time State : Set i) : Set (lsuc i) where
  field
    Admissible : Index → Time → State → Set i

    farLowOperator commutatorOperator multiplierMajorant :
      Index → Time → State → Scalar A

    weightedRowSchur weightedColumnSchur fullOfficialSchur :
      Index → Time → State → Scalar A

    radiusEightOfficialBudget : Index → Time → State → Scalar A

    DivergenceFreeCancellation : Index → Time → State → Set i
    BothLinearizedPlacementsIncluded : Index → Time → State → Set i
    BiotSavartAndLerayMatched : Index → Time → State → Set i
    WeightedSchurFactorization : Index → Time → State → Set i

    divergenceFreeCancellation : ∀ q τ u →
      Admissible q τ u → DivergenceFreeCancellation q τ u

    bothLinearizedPlacementsIncluded : ∀ q τ u →
      Admissible q τ u → BothLinearizedPlacementsIncluded q τ u

    biotSavartAndLerayMatched : ∀ q τ u →
      Admissible q τ u → BiotSavartAndLerayMatched q τ u

    weightedSchurFactorization : ∀ q τ u →
      Admissible q τ u → WeightedSchurFactorization q τ u

    farLowRewrittenAsCommutator : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (farLowOperator q τ u) (commutatorOperator q τ u)

    smoothMultiplierDifferenceBound : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (commutatorOperator q τ u) (multiplierMajorant q τ u)

    officialWeightedSchurBound : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (multiplierMajorant q τ u) (fullOfficialSchur q τ u)

    radiusEightFullConstantFitsBudget : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (fullOfficialSchur q τ u) (radiusEightOfficialBudget q τ u)

    CutoffUniform : Set i
    cutoffUniform : CutoffUniform

open PeriodicFarLowOfficialSchurInputs public

periodicFarLowOfficialRadiusEightEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Time State : Set i} →
  (F : PeriodicFarLowOfficialSchurInputs A Index Time State) →
  ∀ q τ u →
  Admissible F q τ u →
  _≤_ A
    (farLowOperator F q τ u)
    (radiusEightOfficialBudget F q τ u)
periodicFarLowOfficialRadiusEightEstimate {A = A} F q τ u admissible =
  ≤-trans A
    (farLowRewrittenAsCommutator F q τ u admissible)
    (≤-trans A
      (smoothMultiplierDifferenceBound F q τ u admissible)
      (≤-trans A
        (officialWeightedSchurBound F q τ u admissible)
        (radiusEightFullConstantFitsBudget F q τ u admissible)))

------------------------------------------------------------------------
-- Proof-level and fail-closed status.
------------------------------------------------------------------------

farLowCancellationAndTransitivityLevel : ProofLevel
farLowCancellationAndTransitivityLevel = machineChecked

farLowOfficialNormSchurLevel : ProofLevel
farLowOfficialNormSchurLevel = conditional

farLowRadiusEightFullBudgetLevel : ProofLevel
farLowRadiusEightFullBudgetLevel = conditional

farLowOfficialSchurInputsInhabited : Bool
farLowOfficialSchurInputsInhabited = false
