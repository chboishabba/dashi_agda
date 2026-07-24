module DASHI.Physics.Closure.NSPeriodicNearTriadCutoffUniformCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Official cutoff-uniform near-triad theorem surface.
--
-- The exact Fourier split, the three product estimates, the identification of
-- their H1/L2 factors with the selected dissipation and residual quantities, and
-- the common Young-payment comparison are kept in one coherent owner.  The final
-- near estimate is derived only from those proof-relevant inputs.
------------------------------------------------------------------------

record PeriodicNearTriadUniformInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Time State : Set i) : Set (lsuc i) where
  field
    Admissible : Index → Time → State → Set i

    nearTotal nearLowHigh nearHighLow nearHighHigh :
      Index → Time → State → Scalar A

    lowHighUpper highLowUpper highHighUpper officialNearBudget :
      Index → Time → State → Scalar A

    lowHighDissipationPayment lowHighResidualPayment :
      Index → Time → State → Scalar A
    highLowDissipationPayment highLowResidualPayment :
      Index → Time → State → Scalar A
    highHighDissipationPayment highHighResidualPayment :
      Index → Time → State → Scalar A

    exactNearTriadDecomposition : ∀ q τ u →
      nearTotal q τ u ≡
      _+_ A
        (_+_ A (nearLowHigh q τ u) (nearHighLow q τ u))
        (nearHighHigh q τ u)

    lowHighProductEstimate : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (nearLowHigh q τ u) (lowHighUpper q τ u)

    highLowProductEstimate : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (nearHighLow q τ u) (highLowUpper q τ u)

    highHighProductEstimate : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (nearHighHigh q τ u) (highHighUpper q τ u)

    lowHighFactorInterpretation : ∀ q τ u →
      lowHighUpper q τ u ≡
      _+_ A
        (lowHighDissipationPayment q τ u)
        (lowHighResidualPayment q τ u)

    highLowFactorInterpretation : ∀ q τ u →
      highLowUpper q τ u ≡
      _+_ A
        (highLowDissipationPayment q τ u)
        (highLowResidualPayment q τ u)

    highHighFactorInterpretation : ∀ q τ u →
      highHighUpper q τ u ≡
      _+_ A
        (highHighDissipationPayment q τ u)
        (highHighResidualPayment q τ u)

    commonYoungPaymentBudget : ∀ q τ u →
      _≤_ A
        (_+_ A
          (_+_ A (lowHighUpper q τ u) (highLowUpper q τ u))
          (highHighUpper q τ u))
        (officialNearBudget q τ u)

    CutoffUniform : Set i
    cutoffUniform : CutoffUniform

open PeriodicNearTriadUniformInputs public

nearComponentSumBelowUpperSum :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Time State : Set i} →
  (N : PeriodicNearTriadUniformInputs A Index Time State) →
  ∀ q τ u →
  Admissible N q τ u →
  _≤_ A
    (_+_ A
      (_+_ A (nearLowHigh N q τ u) (nearHighLow N q τ u))
      (nearHighHigh N q τ u))
    (_+_ A
      (_+_ A (lowHighUpper N q τ u) (highLowUpper N q τ u))
      (highHighUpper N q τ u))
nearComponentSumBelowUpperSum {A = A} N q τ u admissible =
  ≤-trans A
    (additionMonotoneRight A lowHighHighLow)
    (additionMonotoneLeft A (highHighProductEstimate N q τ u admissible))
  where
  lowHighStep :
    _≤_ A
      (_+_ A (nearLowHigh N q τ u) (nearHighLow N q τ u))
      (_+_ A (lowHighUpper N q τ u) (nearHighLow N q τ u))
  lowHighStep =
    additionMonotoneRight A (lowHighProductEstimate N q τ u admissible)

  highLowStep :
    _≤_ A
      (_+_ A (lowHighUpper N q τ u) (nearHighLow N q τ u))
      (_+_ A (lowHighUpper N q τ u) (highLowUpper N q τ u))
  highLowStep =
    additionMonotoneLeft A (highLowProductEstimate N q τ u admissible)

  lowHighHighLow :
    _≤_ A
      (_+_ A (nearLowHigh N q τ u) (nearHighLow N q τ u))
      (_+_ A (lowHighUpper N q τ u) (highLowUpper N q τ u))
  lowHighHighLow = ≤-trans A lowHighStep highLowStep

periodicNearTriadCutoffUniformEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Time State : Set i} →
  (N : PeriodicNearTriadUniformInputs A Index Time State) →
  ∀ q τ u →
  Admissible N q τ u →
  _≤_ A (nearTotal N q τ u) (officialNearBudget N q τ u)
periodicNearTriadCutoffUniformEstimate {A = A} N q τ u admissible =
  ≤-trans A totalBelowUpper (commonYoungPaymentBudget N q τ u)
  where
  componentBelowUpper :
    _≤_ A
      (_+_ A
        (_+_ A (nearLowHigh N q τ u) (nearHighLow N q τ u))
        (nearHighHigh N q τ u))
      (_+_ A
        (_+_ A (lowHighUpper N q τ u) (highLowUpper N q τ u))
        (highHighUpper N q τ u))
  componentBelowUpper = nearComponentSumBelowUpperSum N q τ u admissible

  totalBelowUpper :
    _≤_ A
      (nearTotal N q τ u)
      (_+_ A
        (_+_ A (lowHighUpper N q τ u) (highLowUpper N q τ u))
        (highHighUpper N q τ u))
  totalBelowUpper =
    subst
      (λ lhs →
        _≤_ A lhs
          (_+_ A
            (_+_ A (lowHighUpper N q τ u) (highLowUpper N q τ u))
            (highHighUpper N q τ u)))
      (sym (exactNearTriadDecomposition N q τ u))
      componentBelowUpper

------------------------------------------------------------------------
-- Proof-level and fail-closed status.
------------------------------------------------------------------------

nearTriadAdditiveAssemblyLevel : ProofLevel
nearTriadAdditiveAssemblyLevel = machineChecked

nearTriadExactFourierFactorInterpretationLevel : ProofLevel
nearTriadExactFourierFactorInterpretationLevel = conditional

nearTriadCutoffUniformProductEstimateLevel : ProofLevel
nearTriadCutoffUniformProductEstimateLevel = conditional

nearTriadOfficialUniformInputsInhabited : Bool
nearTriadOfficialUniformInputsInhabited = false
