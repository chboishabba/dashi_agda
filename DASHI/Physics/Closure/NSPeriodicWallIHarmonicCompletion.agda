module DASHI.Physics.Closure.NSPeriodicWallIHarmonicCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicOfficialNormIdentification as Norm
import DASHI.Physics.Closure.NSPeriodicNearTriadCutoffUniformCompletion as Near
import DASHI.Physics.Closure.NSPeriodicFarLowOfficialSchurCompletion as Low
import DASHI.Physics.Closure.NSPeriodicFarHighTailCompletion as High
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One coherent owner for the official-norm Wall I estimate.
--
-- The official norm identification and the three interaction packages cannot be
-- supplied independently.  Proof-relevant matching fields guarantee that the
-- near, far-low and far-high estimates all concern the same Fourier
-- normalization, dyadic partition, Leray/Biot--Savart operators and cutoff.  The
-- full far-low constant must also be the exact product of the selected weighted
-- row and column Schur factors.
------------------------------------------------------------------------

record PeriodicWallIHarmonicInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Time State : Set i) : Set (lsuc i) where
  field
    officialNorms : Norm.OfficialPeriodicNormIdentification A Index Nat State
    nearInputs : Near.PeriodicNearTriadUniformInputs A Index Time State
    farLowInputs : Low.PeriodicFarLowOfficialSchurInputs A Index Time State
    farHighInputs : High.PeriodicFarHighTailInputs A Index Time State

    farLowSchurFactorCoherence :
      Low.PeriodicFarLowSchurFactorCoherence farLowInputs

    NearUsesOfficialNorms : Set i
    FarLowUsesOfficialNorms : Set i
    FarHighUsesOfficialNorms : Set i

    nearUsesOfficialNorms : NearUsesOfficialNorms
    farLowUsesOfficialNorms : FarLowUsesOfficialNorms
    farHighUsesOfficialNorms : FarHighUsesOfficialNorms

    CommonAdmissible : Index → Time → State → Set i

    commonImpliesNorm : ∀ q τ u →
      CommonAdmissible q τ u → Norm.Admissible officialNorms q u

    commonImpliesNear : ∀ q τ u →
      CommonAdmissible q τ u → Near.Admissible nearInputs q τ u

    commonImpliesFarLow : ∀ q τ u →
      CommonAdmissible q τ u → Low.Admissible farLowInputs q τ u

    commonImpliesFarHigh : ∀ q τ u →
      CommonAdmissible q τ u → High.Admissible farHighInputs q τ u

    nonlinearTotal officialWallIBudget :
      Index → Time → State → Scalar A

    exactNonlinearDecomposition : ∀ q τ u →
      nonlinearTotal q τ u ≡
      _+_ A
        (_+_ A
          (Near.nearTotal nearInputs q τ u)
          (Low.farLowOperator farLowInputs q τ u))
        (High.farHighTotal farHighInputs q τ u)

    componentBudgetsFitOfficialWallI : ∀ q τ u →
      CommonAdmissible q τ u →
      _≤_ A
        (_+_ A
          (_+_ A
            (Near.officialNearBudget nearInputs q τ u)
            (Low.radiusEightOfficialBudget farLowInputs q τ u))
          (High.radiusEightOfficialBudget farHighInputs q τ u))
        (officialWallIBudget q τ u)

open PeriodicWallIHarmonicInputs public

wallIOfficialNormAdmissibility :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Time State : Set i} →
  (W : PeriodicWallIHarmonicInputs A Index Time State) →
  ∀ q τ u →
  CommonAdmissible W q τ u →
  Norm.Admissible (officialNorms W) q u
wallIOfficialNormAdmissibility W q τ u = commonImpliesNorm W q τ u

wallIFarLowSchurProduct :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Time State : Set i} →
  (W : PeriodicWallIHarmonicInputs A Index Time State) →
  ∀ q τ u →
  Low.fullOfficialSchur (farLowInputs W) q τ u ≡
  _∗_ A
    (Low.weightedRowSchur (farLowInputs W) q τ u)
    (Low.weightedColumnSchur (farLowInputs W) q τ u)
wallIFarLowSchurProduct W =
  Low.farLowFullSchurIsRowColumnProduct
    (farLowSchurFactorCoherence W)

wallIComponentSumBelowBudgetSum :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Time State : Set i} →
  (W : PeriodicWallIHarmonicInputs A Index Time State) →
  ∀ q τ u →
  CommonAdmissible W q τ u →
  _≤_ A
    (_+_ A
      (_+_ A
        (Near.nearTotal (nearInputs W) q τ u)
        (Low.farLowOperator (farLowInputs W) q τ u))
      (High.farHighTotal (farHighInputs W) q τ u))
    (_+_ A
      (_+_ A
        (Near.officialNearBudget (nearInputs W) q τ u)
        (Low.radiusEightOfficialBudget (farLowInputs W) q τ u))
      (High.radiusEightOfficialBudget (farHighInputs W) q τ u))
wallIComponentSumBelowBudgetSum {A = A} W q τ u admissible =
  ≤-trans A
    (additionMonotoneRight A nearLow)
    (additionMonotoneLeft A high)
  where
  near :
    _≤_ A
      (Near.nearTotal (nearInputs W) q τ u)
      (Near.officialNearBudget (nearInputs W) q τ u)
  near = Near.periodicNearTriadCutoffUniformEstimate
    (nearInputs W) q τ u (commonImpliesNear W q τ u admissible)

  low :
    _≤_ A
      (Low.farLowOperator (farLowInputs W) q τ u)
      (Low.radiusEightOfficialBudget (farLowInputs W) q τ u)
  low = Low.periodicFarLowOfficialRadiusEightEstimate
    (farLowInputs W) q τ u (commonImpliesFarLow W q τ u admissible)

  high :
    _≤_ A
      (High.farHighTotal (farHighInputs W) q τ u)
      (High.radiusEightOfficialBudget (farHighInputs W) q τ u)
  high = High.periodicFarHighOfficialRadiusEightEstimate
    (farHighInputs W) q τ u (commonImpliesFarHigh W q τ u admissible)

  nearStep :
    _≤_ A
      (_+_ A
        (Near.nearTotal (nearInputs W) q τ u)
        (Low.farLowOperator (farLowInputs W) q τ u))
      (_+_ A
        (Near.officialNearBudget (nearInputs W) q τ u)
        (Low.farLowOperator (farLowInputs W) q τ u))
  nearStep = additionMonotoneRight A near

  lowStep :
    _≤_ A
      (_+_ A
        (Near.officialNearBudget (nearInputs W) q τ u)
        (Low.farLowOperator (farLowInputs W) q τ u))
      (_+_ A
        (Near.officialNearBudget (nearInputs W) q τ u)
        (Low.radiusEightOfficialBudget (farLowInputs W) q τ u))
  lowStep = additionMonotoneLeft A low

  nearLow :
    _≤_ A
      (_+_ A
        (Near.nearTotal (nearInputs W) q τ u)
        (Low.farLowOperator (farLowInputs W) q τ u))
      (_+_ A
        (Near.officialNearBudget (nearInputs W) q τ u)
        (Low.radiusEightOfficialBudget (farLowInputs W) q τ u))
  nearLow = ≤-trans A nearStep lowStep

periodicWallIHarmonicEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Time State : Set i} →
  (W : PeriodicWallIHarmonicInputs A Index Time State) →
  ∀ q τ u →
  CommonAdmissible W q τ u →
  _≤_ A
    (nonlinearTotal W q τ u)
    (officialWallIBudget W q τ u)
periodicWallIHarmonicEstimate {A = A} W q τ u admissible =
  ≤-trans A totalBelowComponents
    (componentBudgetsFitOfficialWallI W q τ u admissible)
  where
  totalBelowComponents :
    _≤_ A
      (nonlinearTotal W q τ u)
      (_+_ A
        (_+_ A
          (Near.officialNearBudget (nearInputs W) q τ u)
          (Low.radiusEightOfficialBudget (farLowInputs W) q τ u))
        (High.radiusEightOfficialBudget (farHighInputs W) q τ u))
  totalBelowComponents =
    subst
      (λ lhs →
        _≤_ A lhs
          (_+_ A
            (_+_ A
              (Near.officialNearBudget (nearInputs W) q τ u)
              (Low.radiusEightOfficialBudget (farLowInputs W) q τ u))
            (High.radiusEightOfficialBudget (farHighInputs W) q τ u)))
      (sym (exactNonlinearDecomposition W q τ u))
      (wallIComponentSumBelowBudgetSum W q τ u admissible)

------------------------------------------------------------------------
-- Proof-level and fail-closed status.
------------------------------------------------------------------------

wallIHarmonicAssemblyLevel : ProofLevel
wallIHarmonicAssemblyLevel = machineChecked

wallIOfficialNormInputsLevel : ProofLevel
wallIOfficialNormInputsLevel = conditional

wallIOfficialHarmonicInputsInhabited : Bool
wallIOfficialHarmonicInputsInhabited = false
