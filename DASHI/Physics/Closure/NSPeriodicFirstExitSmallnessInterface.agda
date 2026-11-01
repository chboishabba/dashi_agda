module DASHI.Physics.Closure.NSPeriodicFirstExitSmallnessInterface where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- First-exit smallness interface for the three near Bony lanes.
--
-- Admissibility is proposition-valued.  The geometric/trajectory predicate,
-- the dimensionless analytic observable, the lane estimate, and the scalar
-- budget comparison are separate fields.  The final 1/16,1/16,1/8 estimates
-- are derived by order transitivity rather than stored as assumptions.
------------------------------------------------------------------------

record FirstExitSmallnessInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Time State : Set i) : Set (lsuc i) where
  field
    Admissible : Index → Time → State → Set i

    depletion : Index → Time → State → Scalar A
    epsilonGamma : Scalar A
    epsilonGammaNonnegative : _≤_ A (zero A) epsilonGamma

    dissipation : Index → Time → State → Scalar A

    lowHighNonlinear highLowNonlinear highHighNonlinear :
      Index → Time → State → Scalar A

    lowHighRemainder highLowRemainder highHighRemainder :
      Index → Time → State → Scalar A

    lowHighConstant highLowConstant highHighConstant : Scalar A
    lowHighShare highLowShare highHighShare : Scalar A

    coefficientTimes : Scalar A → Scalar A → Scalar A
    scaleDissipation : Scalar A → Scalar A → Scalar A

    coefficientTimesMonotoneRight : ∀ {coefficient μ ε} →
      _≤_ A μ ε →
      _≤_ A
        (coefficientTimes coefficient μ)
        (coefficientTimes coefficient ε)

    scaleDissipationMonotoneLeft : ∀ {left right D} →
      _≤_ A left right →
      _≤_ A
        (scaleDissipation left D)
        (scaleDissipation right D)

    admissibleImpliesSmall : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (depletion q τ u) epsilonGamma

    lowHighFromDepletion : ∀ q τ u →
      _≤_ A
        (lowHighNonlinear q τ u)
        (_+_ A
          (scaleDissipation
            (coefficientTimes lowHighConstant (depletion q τ u))
            (dissipation q τ u))
          (lowHighRemainder q τ u))

    highLowFromDepletion : ∀ q τ u →
      _≤_ A
        (highLowNonlinear q τ u)
        (_+_ A
          (scaleDissipation
            (coefficientTimes highLowConstant (depletion q τ u))
            (dissipation q τ u))
          (highLowRemainder q τ u))

    highHighFromDepletion : ∀ q τ u →
      _≤_ A
        (highHighNonlinear q τ u)
        (_+_ A
          (scaleDissipation
            (coefficientTimes highHighConstant (depletion q τ u))
            (dissipation q τ u))
          (highHighRemainder q τ u))

    lowHighScalarBudget :
      _≤_ A
        (coefficientTimes lowHighConstant epsilonGamma)
        lowHighShare

    highLowScalarBudget :
      _≤_ A
        (coefficientTimes highLowConstant epsilonGamma)
        highLowShare

    highHighScalarBudget :
      _≤_ A
        (coefficientTimes highHighConstant epsilonGamma)
        highHighShare

open FirstExitSmallnessInputs public

weightedDepletionBelowEpsilon :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (I : FirstExitSmallnessInputs A Index Time State) →
  ∀ coefficient q τ u → Admissible I q τ u →
  _≤_ A
    (scaleDissipation I
      (coefficientTimes I coefficient (depletion I q τ u))
      (dissipation I q τ u))
    (scaleDissipation I
      (coefficientTimes I coefficient (epsilonGamma I))
      (dissipation I q τ u))
weightedDepletionBelowEpsilon I coefficient q τ u admissible =
  scaleDissipationMonotoneLeft I
    (coefficientTimesMonotoneRight I
      (admissibleImpliesSmall I q τ u admissible))

lowHighCanonicalShareEstimate :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (I : FirstExitSmallnessInputs A Index Time State) →
  ∀ q τ u → Admissible I q τ u →
  _≤_ A
    (lowHighNonlinear I q τ u)
    (_+_ A
      (scaleDissipation I (lowHighShare I) (dissipation I q τ u))
      (lowHighRemainder I q τ u))
lowHighCanonicalShareEstimate {A = A} I q τ u admissible =
  ≤-trans A
    (lowHighFromDepletion I q τ u)
    (≤-trans A
      (additionMonotoneRight A
        (weightedDepletionBelowEpsilon I
          (lowHighConstant I) q τ u admissible))
      (additionMonotoneRight A
        (scaleDissipationMonotoneLeft I (lowHighScalarBudget I))))

highLowCanonicalShareEstimate :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (I : FirstExitSmallnessInputs A Index Time State) →
  ∀ q τ u → Admissible I q τ u →
  _≤_ A
    (highLowNonlinear I q τ u)
    (_+_ A
      (scaleDissipation I (highLowShare I) (dissipation I q τ u))
      (highLowRemainder I q τ u))
highLowCanonicalShareEstimate {A = A} I q τ u admissible =
  ≤-trans A
    (highLowFromDepletion I q τ u)
    (≤-trans A
      (additionMonotoneRight A
        (weightedDepletionBelowEpsilon I
          (highLowConstant I) q τ u admissible))
      (additionMonotoneRight A
        (scaleDissipationMonotoneLeft I (highLowScalarBudget I))))

highHighCanonicalShareEstimate :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (I : FirstExitSmallnessInputs A Index Time State) →
  ∀ q τ u → Admissible I q τ u →
  _≤_ A
    (highHighNonlinear I q τ u)
    (_+_ A
      (scaleDissipation I (highHighShare I) (dissipation I q τ u))
      (highHighRemainder I q τ u))
highHighCanonicalShareEstimate {A = A} I q τ u admissible =
  ≤-trans A
    (highHighFromDepletion I q τ u)
    (≤-trans A
      (additionMonotoneRight A
        (weightedDepletionBelowEpsilon I
          (highHighConstant I) q τ u admissible))
      (additionMonotoneRight A
        (scaleDissipationMonotoneLeft I (highHighScalarBudget I))))

------------------------------------------------------------------------
-- Optional candidate-observable registration.  This record names the factors
-- of a proposed geometric coefficient without asserting any evolution or
-- smallness theorem for them.
------------------------------------------------------------------------

record CandidateGeometricDepletionObservable
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Time State : Set i) : Set (lsuc i) where
  field
    topologicalCurrentFactor : Index → Time → State → Scalar A
    enstrophyOneFifthFactor : Index → Time → State → Scalar A
    inverseVorticityOneTenthFactor : Index → Time → State → Scalar A

    combineThree : Scalar A → Scalar A → Scalar A → Scalar A
    candidateDepletion : Index → Time → State → Scalar A

    candidateMeaning : ∀ q τ u →
      candidateDepletion q τ u
      ≡ combineThree
          (topologicalCurrentFactor q τ u)
          (enstrophyOneFifthFactor q τ u)
          (inverseVorticityOneTenthFactor q τ u)

open CandidateGeometricDepletionObservable public

firstExitSmallnessReductionLevel : ProofLevel
firstExitSmallnessReductionLevel = machineChecked

firstExitAdmissibleImpliesSmallLevel : ProofLevel
firstExitAdmissibleImpliesSmallLevel = conditional

candidateTopologicalDepletionInstanceLevel : ProofLevel
candidateTopologicalDepletionInstanceLevel = conditional
