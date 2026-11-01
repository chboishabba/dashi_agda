module DASHI.Physics.Closure.NSCompactGammaConcreteFarTail where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaOffPacketTailDecayBridge as Tail

------------------------------------------------------------------------
-- TL1. Exact divergence-free Fourier cancellation.
------------------------------------------------------------------------

record FourierCancellationAlgebra
    {m v s : Level}
    (Mode : Set m)
    (Vector : Set v)
    (Scalar : Set s) : Set (lsuc (m Agda.Primitive.⊔ v Agda.Primitive.⊔ s)) where
  field
    _-_ : Mode → Mode → Mode
    _·_ : Vector → Mode → Scalar
    zeroS : Scalar

    dotDifference :
      (u : Vector) (k p : Mode) →
      _·_ u (_-_ k p) ≡ subtractScalar (_·_ u k) (_·_ u p)

    subtractScalar : Scalar → Scalar → Scalar
    subtractZeroRight : (a : Scalar) → subtractScalar a zeroS ≡ a

open FourierCancellationAlgebra public

fourierDivergenceFreeCancellation :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  (A : FourierCancellationAlgebra Mode Vector Scalar) →
  (u : Vector) (p q k : Mode) →
  q ≡ _-_ A k p →
  _·_ A u p ≡ zeroS A →
  _·_ A u q ≡ _·_ A u k
fourierDivergenceFreeCancellation A u p q k q=k-p divFree =
  trans
    (cong (_·_ A u) q=k-p)
    (trans
      (dotDifference A u k p)
      (trans
        (cong (subtractScalar A (_·_ A u k)) divFree)
        (subtractZeroRight A (_·_ A u k))))

------------------------------------------------------------------------
-- TL2. Exact target-shell multiplier commutator identity.
------------------------------------------------------------------------

record MultiplierCommutatorIdentity
    {a : Level}
    (A : AbsorptionArithmetic)
    (Atom : Set a) : Set (lsuc a) where
  field
    targetShellCoefficient : Atom → Scalar A
    transportedCoefficient : Atom → Scalar A
    commutatorCoefficient : Atom → Scalar A

    exactCoefficientDifference :
      (atom : Atom) →
      commutatorCoefficient atom ≡
      targetShellCoefficient atom

    -- The concrete atom evaluator includes
    -- i (uHat(p) dot q) (mK(k) - mK(q)) hHat(q).
    -- This equality is deliberately attached to the evaluator used by the
    -- differentiated compact-Gamma numerator, rather than to a second model.
    transportedEqualsTargetDifference :
      (atom : Atom) →
      transportedCoefficient atom ≡ commutatorCoefficient atom

open MultiplierCommutatorIdentity public

multiplierCommutatorCoefficientIsExact :
  ∀ {a} {A : AbsorptionArithmetic} {Atom : Set a} →
  (I : MultiplierCommutatorIdentity A Atom) →
  (atom : Atom) →
  transportedCoefficient I atom ≡ targetShellCoefficient I atom
multiplierCommutatorCoefficientIsExact I atom =
  trans
    (transportedEqualsTargetDifference I atom)
    (exactCoefficientDifference I atom)

------------------------------------------------------------------------
-- Smooth shell multiplier gain and TL3 commutator estimate.
------------------------------------------------------------------------

record SmoothShellMultiplierGain
    (A : AbsorptionArithmetic) : Set₁ where
  field
    multiplierDifference : Scalar A
    derivativeScaleGain : Scalar A
    lowFrequencyScale : Scalar A
    dyadicRadiusGain : Scalar A

    meanValueBound :
      _≤_ A multiplierDifference
        (_+_ A derivativeScaleGain lowFrequencyScale)

    separatedScalesGive2^-R :
      _≤_ A
        (_+_ A derivativeScaleGain lowFrequencyScale)
        dyadicRadiusGain

open SmoothShellMultiplierGain public

smoothMultiplierDifferenceDecays :
  (A : AbsorptionArithmetic) →
  (G : SmoothShellMultiplierGain A) →
  _≤_ A (multiplierDifference G) (dyadicRadiusGain G)
smoothMultiplierDifferenceDecays A G =
  ≤-trans A (meanValueBound G) (separatedScalesGive2^-R G)

record FarLowCommutatorBound
    (A : AbsorptionArithmetic)
    (M : Tail.TailProductArithmetic A) : Set₁ where
  field
    commutatorNorm : Scalar A
    radiusGain : Scalar A
    lowVelocityNorm : Scalar A
    tangentShellNorm : Scalar A

    rawCommutatorEstimate :
      _≤_ A commutatorNorm
        (Tail._·_ M radiusGain
          (Tail._·_ M lowVelocityNorm tangentShellNorm))

open FarLowCommutatorBound public

------------------------------------------------------------------------
-- TL4 and TL5. Leray and compact-Gamma tangent stability.
------------------------------------------------------------------------

record LerayProjectionStability
    (A : AbsorptionArithmetic)
    (M : Tail.TailProductArithmetic A) : Set₁ where
  field
    unprojectedNorm projectedNorm projectionConstant : Scalar A

    l2Contraction : _≤_ A projectedNorm unprojectedNorm
    weightedStability :
      _≤_ A projectedNorm
        (Tail._·_ M projectionConstant unprojectedNorm)

open LerayProjectionStability public

record TangentCorrectionStability
    (A : AbsorptionArithmetic)
    (M : Tail.TailProductArithmetic A) : Set₁ where
  field
    inputNorm correctedNorm tangentConstant : Scalar A

    tangentProjectionUniformOnAdmissibleClass :
      _≤_ A correctedNorm
        (Tail._·_ M tangentConstant inputNorm)

open TangentCorrectionStability public

record CorrectedFarLowEstimate
    (A : AbsorptionArithmetic)
    (M : Tail.TailProductArithmetic A) : Set₁ where
  field
    raw : FarLowCommutatorBound A M
    leray : LerayProjectionStability A M
    tangent : TangentCorrectionStability A M

    lerayInputMatchesRaw :
      unprojectedNorm leray ≡ commutatorNorm raw

    tangentInputMatchesLeray :
      inputNorm tangent ≡ projectedNorm leray

    correctedLowBudget : Scalar A

    stabilityConstantsAbsorbed :
      _≤_ A
        (Tail._·_ M (tangentConstant tangent)
          (Tail._·_ M (projectionConstant leray)
            (Tail._·_ M (radiusGain raw)
              (Tail._·_ M (lowVelocityNorm raw) (tangentShellNorm raw)))))
        correctedLowBudget

open CorrectedFarLowEstimate public

correctedFarLowDecay :
  (A : AbsorptionArithmetic) →
  (M : Tail.TailProductArithmetic A) →
  (I : CorrectedFarLowEstimate A M) →
  _≤_ A (correctedNorm (tangent I)) (correctedLowBudget I)
correctedFarLowDecay A M I =
  ≤-trans A
    (tangentProjectionUniformOnAdmissibleClass (tangent I))
    (≤-trans A tangentToLerayBudget
      (stabilityConstantsAbsorbed I))
  where
  tangentToLerayBudget :
    _≤_ A
      (Tail._·_ M (tangentConstant (tangent I))
        (inputNorm (tangent I)))
      (Tail._·_ M (tangentConstant (tangent I))
        (Tail._·_ M (projectionConstant (leray I))
          (Tail._·_ M (radiusGain (raw I))
            (Tail._·_ M
              (lowVelocityNorm (raw I))
              (tangentShellNorm (raw I)))))
  tangentToLerayBudget
    rewrite tangentInputMatchesLeray I
          | lerayInputMatchesRaw I =
    Tail.multiplicationMonotoneLeft M
      (≤-trans A
        (weightedStability (leray I))
        (Tail.multiplicationMonotoneLeft M
          (rawCommutatorEstimate (raw I))))

------------------------------------------------------------------------
-- TH1 and TH2. High-frequency Sobolev and paraproduct decay.
------------------------------------------------------------------------

record HighFrequencySobolevTail
    (A : AbsorptionArithmetic) : Set₁ where
  field
    highTailNorm : Scalar A
    fullSobolevNorm : Scalar A
    absoluteScaleDecay : Scalar A
    relativeRadiusDecay : Scalar A

    highTailSobolevBound :
      _≤_ A highTailNorm absoluteScaleDecay

    targetRescalingProducesRadiusDecay :
      _≤_ A absoluteScaleDecay relativeRadiusDecay

    radiusDecayBelowFullSobolevBudget :
      _≤_ A relativeRadiusDecay fullSobolevNorm

open HighFrequencySobolevTail public

highFrequencySobolevDecay :
  (A : AbsorptionArithmetic) →
  (H : HighFrequencySobolevTail A) →
  _≤_ A (highTailNorm H) (fullSobolevNorm H)
highFrequencySobolevDecay A H =
  ≤-trans A (highTailSobolevBound H)
    (≤-trans A (targetRescalingProducesRadiusDecay H)
      (radiusDecayBelowFullSobolevBudget H))

record FarHighParaproductBound
    (A : AbsorptionArithmetic) : Set₁ where
  field
    leftHighResponse rightHighResponse : Scalar A
    summedHighResponse highDecayBudget : Scalar A
    exponentAlpha : Scalar A

    twoPlacementsAssemble :
      _≤_ A summedHighResponse
        (_+_ A leftHighResponse rightHighResponse)

    leftPlacementDecay :
      _≤_ A leftHighResponse highDecayBudget

    rightPlacementDecay :
      _≤_ A rightHighResponse highDecayBudget

    duplicatedBudgetAbsorbed :
      _≤_ A (_+_ A highDecayBudget highDecayBudget) highDecayBudget

open FarHighParaproductBound public

farHighParaproductDecay :
  (A : AbsorptionArithmetic) →
  (H : FarHighParaproductBound A) →
  _≤_ A (summedHighResponse H) (highDecayBudget H)
farHighParaproductDecay A H =
  ≤-trans A (twoPlacementsAssemble H)
    (≤-trans A
      (≤-trans A
        (additionMonotoneRight A (leftPlacementDecay H))
        (additionMonotoneLeft A (rightPlacementDecay H)))
      (duplicatedBudgetAbsorbed H))

------------------------------------------------------------------------
-- TH3. Differentiated compact-Gamma numerator domination.
------------------------------------------------------------------------

record DifferentiatedFarNumeratorDomination
    (A : AbsorptionArithmetic) : Set₁ where
  field
    differentiatedFarNumerator : Scalar A
    farLowContribution farHighContribution : Scalar A
    lowBudget highBudget totalFarBudget : Scalar A

    numeratorSplitsLowHigh :
      _≤_ A differentiatedFarNumerator
        (_+_ A farLowContribution farHighContribution)

    farLowDominated : _≤_ A farLowContribution lowBudget
    farHighDominated : _≤_ A farHighContribution highBudget

    lowPlusHighIsDisplayedRate :
      _≤_ A (_+_ A lowBudget highBudget) totalFarBudget

open DifferentiatedFarNumeratorDomination public

differentiatedFarNumeratorBound :
  (A : AbsorptionArithmetic) →
  (D : DifferentiatedFarNumeratorDomination A) →
  _≤_ A (differentiatedFarNumerator D) (totalFarBudget D)
differentiatedFarNumeratorBound A D =
  ≤-trans A (numeratorSplitsLowHigh D)
    (≤-trans A
      (≤-trans A
        (additionMonotoneRight A (farLowDominated D))
        (additionMonotoneLeft A (farHighDominated D)))
      (lowPlusHighIsDisplayedRate D))

------------------------------------------------------------------------
-- T1--T3. Uniform epsilon(R) endpoint.
------------------------------------------------------------------------

record ConcreteTailRate
    {r : Level}
    {Radius : Set r}
    (A : AbsorptionArithmetic) : Set (lsuc r) where
  field
    _≤R_ : Radius → Radius → Set
    epsilon lowRate highRate : Radius → Scalar A

    epsilonIsLowPlusHigh :
      (R : Radius) → epsilon R ≡ _+_ A (lowRate R) (highRate R)

    lowMonotone :
      {R₁ R₂ : Radius} → _≤R_ R₁ R₂ → _≤_ A (lowRate R₂) (lowRate R₁)

    highMonotone :
      {R₁ R₂ : Radius} → _≤R_ R₁ R₂ → _≤_ A (highRate R₂) (highRate R₁)

    AdmissiblePositiveBudget : Scalar A → Set

    explicitRadius : Scalar A → Radius

    lowEventuallyHalfBudget :
      (delta : Scalar A) → AdmissiblePositiveBudget delta →
      _≤_ A (lowRate (explicitRadius delta)) delta

    highEventuallyHalfBudget :
      (delta : Scalar A) → AdmissiblePositiveBudget delta →
      _≤_ A (highRate (explicitRadius delta)) delta

open ConcreteTailRate public

tailRateMonotone :
  ∀ {r} {Radius : Set r}
    (A : AbsorptionArithmetic) →
  (E : ConcreteTailRate {Radius = Radius} A) →
  {R₁ R₂ : Radius} → _≤R_ E R₁ R₂ →
  _≤_ A (epsilon E R₂) (epsilon E R₁)
tailRateMonotone A E R₁≤R₂ =
  subst (λ x → _≤_ A x (epsilon E _)) (sym (epsilonIsLowPlusHigh E _))
    (subst (λ x → _≤_ A (_+_ A (lowRate E _) (highRate E _)) x)
      (sym (epsilonIsLowPlusHigh E _))
      (≤-trans A
        (additionMonotoneRight A (lowMonotone E R₁≤R₂))
        (additionMonotoneLeft A (highMonotone E R₁≤R₂))))

record CutoffUniformAnalyticTailDecay
    {r k n u h : Level}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (M : Tail.TailProductArithmetic A)
    (Shell : Set k)
    (Cutoff : Set n)
    (State : Set u)
    (Tangent : Set h) : Set (lsuc (r Agda.Primitive.⊔ k Agda.Primitive.⊔ n Agda.Primitive.⊔ u Agda.Primitive.⊔ h)) where
  field
    rate : ConcreteTailRate {Radius = Radius} A
    Admissible : State → Set
    TangentAt : State → Tangent → Set
    shellEnergy : Shell → State → Scalar A
    tangentNorm : Shell → Tangent → Scalar A
    tail : Shell → Cutoff → Radius → State → Tangent → Scalar A

    uniformTailBound :
      (K : Shell) (N : Cutoff) (R : Radius)
      (state : State) (direction : Tangent) →
      Admissible state → TangentAt state direction →
      _≤_ A (tail K N R state direction)
        (Tail._·_ M (epsilon rate R)
          (Tail._·_ M (shellEnergy K state) (tangentNorm K direction)))

open CutoffUniformAnalyticTailDecay public

cutoffUniformAnalyticTailDecay :
  ∀ {r k n u h}
    {Radius : Set r} {Shell : Set k} {Cutoff : Set n}
    {State : Set u} {Tangent : Set h}
    {A : AbsorptionArithmetic} {M : Tail.TailProductArithmetic A} →
  (T : CutoffUniformAnalyticTailDecay A M Shell Cutoff State Tangent) →
  (K : Shell) (N : Cutoff) (R : Radius)
  (state : State) (direction : Tangent) →
  Admissible T state → TangentAt T state direction →
  _≤_ A (tail T K N R state direction)
    (Tail._·_ M (epsilon (rate T) R)
      (Tail._·_ M (shellEnergy T K state) (tangentNorm T K direction)))
cutoffUniformAnalyticTailDecay T = uniformTailBound T
