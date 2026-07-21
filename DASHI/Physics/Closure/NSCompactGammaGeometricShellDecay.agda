module DASHI.Physics.Closure.NSCompactGammaGeometricShellDecay where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- Multiplicative ordered structure used by the geometric shell recurrence.
--
-- This module repairs the earlier additive coefficient recursion.  A genuine
-- shell-decay iteration is now tied to
--
--   a (n + 1) <= rho * a n + r n,
--
-- with rho < 1 and a closed bound satisfying the same multiplicative
-- recurrence.  No theorem can obtain geometric decay from the old linear
-- coefficient growth C (n + 1) = c + C n.
------------------------------------------------------------------------

record OrderedSemiringExtension (A : AbsorptionArithmetic) : Set₁ where
  field
    one : Scalar A
    _*_ : Scalar A → Scalar A → Scalar A
    power : Scalar A → Nat → Scalar A
    StrictlyBelow : Scalar A → Scalar A → Set

    powerZero : ∀ x → power x zero ≡ one
    powerStep : ∀ x n → power x (suc n) ≡ _*_ x (power x n)

    multiplicationMonotoneLeft : ∀ c {a b} →
      _≤_ A a b → _≤_ A (_*_ c a) (_*_ c b)

    additionMonotoneBoth : ∀ {a a′ b b′} →
      _≤_ A a a′ → _≤_ A b b′ →
      _≤_ A (_+_ A a b) (_+_ A a′ b′)

open OrderedSemiringExtension public

record ReflexiveOrderExtension (A : AbsorptionArithmetic) : Set₁ where
  field
    reflexive : ∀ x → _≤_ A x x

open ReflexiveOrderExtension public

------------------------------------------------------------------------
-- Explicit finite geometric convolution
--
--   r(n-1) + rho r(n-2) + ... + rho^(n-1) r(0).
------------------------------------------------------------------------

weightedGeometricRemainder :
  ∀ {A : AbsorptionArithmetic} →
  OrderedSemiringExtension A →
  Scalar A → (Nat → Scalar A) → Nat → Scalar A
weightedGeometricRemainder {A} M rho r zero = zero A
weightedGeometricRemainder {A} M rho r (suc n) =
  _+_ A
    (_*_ M rho (weightedGeometricRemainder M rho r n))
    (r n)

geometricClosedForm :
  ∀ {A : AbsorptionArithmetic} →
  (M : OrderedSemiringExtension A) →
  Scalar A → Scalar A → (Nat → Scalar A) → Nat → Scalar A
geometricClosedForm {A} M rho envelope r n =
  _+_ A
    (_*_ M (power M rho n) envelope)
    (weightedGeometricRemainder M rho r n)

------------------------------------------------------------------------
-- SD5. Exact multiplicative iteration.
------------------------------------------------------------------------

record GeometricRecurrence
    (A : AbsorptionArithmetic)
    (M : OrderedSemiringExtension A) : Set₁ where
  field
    value remainder closedBound : Nat → Scalar A
    envelope rho : Scalar A

    rhoStrict : StrictlyBelow M rho (one M)

    initialBound : _≤_ A (value zero) envelope

    oneStepBound : ∀ n →
      _≤_ A
        (value (suc n))
        (_+_ A (_*_ M rho (value n)) (remainder n))

    closedZero : closedBound zero ≡ envelope
    closedStep : ∀ n →
      closedBound (suc n) ≡
      _+_ A (_*_ M rho (closedBound n)) (remainder n)

    -- The concrete scalar instance proves that the recurrence above is exactly
    -- the usual rho^n initial term plus the finite weighted remainder sum.
    closedFormIdentity : ∀ n →
      closedBound n ≡
      geometricClosedForm M rho envelope remainder n

open GeometricRecurrence public

iterateAdjacentGeometricDecay :
  ∀ {A : AbsorptionArithmetic}
    {M : OrderedSemiringExtension A} →
  ReflexiveOrderExtension A →
  (R : GeometricRecurrence A M) →
  ∀ n → _≤_ A (value R n) (closedBound R n)
iterateAdjacentGeometricDecay {A} {M} O R zero =
  subst
    (λ upper → _≤_ A (value R zero) upper)
    (sym (closedZero R))
    (initialBound R)
iterateAdjacentGeometricDecay {A} {M} O R (suc n) =
  ≤-trans A
    (oneStepBound R n)
    (subst
      (λ upper →
        _≤_ A
          (_+_ A (_*_ M (rho R) (value R n)) (remainder R n))
          upper)
      (sym (closedStep R n))
      (additionMonotoneBoth M
        (multiplicationMonotoneLeft M (rho R)
          (iterateAdjacentGeometricDecay O R n))
        (reflexive O (remainder R n))))

iterateAdjacentGeometricDecayExplicit :
  ∀ {A : AbsorptionArithmetic}
    {M : OrderedSemiringExtension A} →
  ReflexiveOrderExtension A →
  (R : GeometricRecurrence A M) →
  ∀ n →
  _≤_ A
    (value R n)
    (geometricClosedForm M (rho R) (envelope R) (remainder R) n)
iterateAdjacentGeometricDecayExplicit {A} {M} O R n =
  subst
    (λ upper → _≤_ A (value R n) upper)
    (closedFormIdentity R n)
    (iterateAdjacentGeometricDecay O R n)

------------------------------------------------------------------------
-- SD1--SD4: exact Fourier-shell producer obligations.
------------------------------------------------------------------------

record FourierShellDynamics
    (A : AbsorptionArithmetic)
    (M : OrderedSemiringExtension A) : Set₁ where
  field
    Index Time State Shell TriadClass : Set

    selectedState : Index → Time → State
    targetShell : Index → Shell

    shellEnergy shellGradientEnergy shellNonlinearPairing :
      Shell → State → Scalar A
    shellEnergyDerivative : Index → Shell → Time → Scalar A
    viscosity : Scalar A

    lowHigh nearNear highLow : TriadClass
    triadsFeeding : Shell → TriadClass → Set

    weightedFiveHalvesShell : Shell → State → Scalar A
    highRemainder lowRemainder : Index → Time → Nat → Scalar A
    highValue lowValue : Index → Time → Nat → Scalar A
    rho : Scalar A

    -- SD1.
    fourierShellEnergyDerivative : ∀ q j τ →
      shellEnergyDerivative q j τ ≡
      _+_ A
        (_*_ M viscosity (shellGradientEnergy j (selectedState q τ)))
        (shellNonlinearPairing j (selectedState q τ))

    -- SD2.  The producer must prove that these are the complete interaction
    -- classes feeding the target shell; the type does not silently discard a
    -- fourth case.
    targetShellTriadsSplit : ∀ j →
      (triadsFeeding j lowHigh)
      ⊎ ((triadsFeeding j nearNear) ⊎ (triadsFeeding j highLow))

    -- SD3.
    fourierTriadsGiveAdjacentHighShellDecay : ∀ q τ n →
      _≤_ A
        (highValue q τ (suc n))
        (_+_ A (_*_ M rho (highValue q τ n)) (highRemainder q τ n))

    fourierTriadsGiveAdjacentLowShellDecay : ∀ q τ n →
      _≤_ A
        (lowValue q τ (suc n))
        (_+_ A (_*_ M rho (lowValue q τ n)) (lowRemainder q τ n))

    -- SD4.
    adjacentShellDecayFactorStrict : StrictlyBelow M rho (one M)

open FourierShellDynamics public

------------------------------------------------------------------------
-- SD6--SD7: two-sided geometric assembly.
------------------------------------------------------------------------

record TwoSidedGeometricShellDecay
    (A : AbsorptionArithmetic)
    (M : OrderedSemiringExtension A)
    (O : ReflexiveOrderExtension A)
    (D : FourierShellDynamics A M) : Set₁ where
  field
    leftRecurrence rightRecurrence :
      (q : Index D) → (τ : Time D) → GeometricRecurrence A M

    leftValueMeaning : ∀ q τ n →
      value (leftRecurrence q τ) n ≡ lowValue D q τ n

    rightValueMeaning : ∀ q τ n →
      value (rightRecurrence q τ) n ≡ highValue D q τ n

    ShellSide : Set
    leftSide rightSide : ShellSide
    sideOf : Index D → Shell D → ShellSide
    distanceFromTarget : Index D → Shell D → Nat

    leftShellMeaning : ∀ q j τ → sideOf q j ≡ leftSide →
      weightedFiveHalvesShell D j (selectedState D q τ) ≡
      value (leftRecurrence q τ) (distanceFromTarget q j)

    rightShellMeaning : ∀ q j τ → sideOf q j ≡ rightSide →
      weightedFiveHalvesShell D j (selectedState D q τ) ≡
      value (rightRecurrence q τ) (distanceFromTarget q j)

    sideComplete : ∀ q j →
      (sideOf q j ≡ leftSide) ⊎ (sideOf q j ≡ rightSide)

    decayCoefficient : Index D → Shell D → Scalar A
    compactGammaEnvelope : Index D → Time D → Scalar A

    leftClosedIdentifiesCoefficientEnvelope : ∀ q j τ →
      sideOf q j ≡ leftSide →
      closedBound (leftRecurrence q τ) (distanceFromTarget q j) ≡
      _+_ A (decayCoefficient q j) (compactGammaEnvelope q τ)

    rightClosedIdentifiesCoefficientEnvelope : ∀ q j τ →
      sideOf q j ≡ rightSide →
      closedBound (rightRecurrence q τ) (distanceFromTarget q j) ≡
      _+_ A (decayCoefficient q j) (compactGammaEnvelope q τ)

    weightedShellSum coefficientSum uniformCoefficientBound :
      Index D → Time D → Scalar A

    shellDecayRemaindersSummable : ∀ q τ →
      _≤_ A (coefficientSum q τ) (uniformCoefficientBound q τ)

    sumPointwiseDecay :
      (∀ q j τ →
        _≤_ A
          (weightedFiveHalvesShell D j (selectedState D q τ))
          (_+_ A (decayCoefficient q j) (compactGammaEnvelope q τ))) →
      ∀ q τ →
      _≤_ A (weightedShellSum q τ) (compactGammaEnvelope q τ)

open TwoSidedGeometricShellDecay public

leftShellGeometricDecay :
  ∀ {A : AbsorptionArithmetic}
    {M : OrderedSemiringExtension A}
    {O : ReflexiveOrderExtension A}
    {D : FourierShellDynamics A M} →
  (T : TwoSidedGeometricShellDecay A M O D) →
  ∀ q j τ → sideOf T q j ≡ leftSide T →
  _≤_ A
    (weightedFiveHalvesShell D j (selectedState D q τ))
    (_+_ A (decayCoefficient T q j) (compactGammaEnvelope T q τ))
leftShellGeometricDecay {A} {M} {O} {D} T q j τ side =
  subst
    (λ lower →
      _≤_ A lower
        (_+_ A (decayCoefficient T q j) (compactGammaEnvelope T q τ)))
    (sym (leftShellMeaning T q j τ side))
    (subst
      (λ upper →
        _≤_ A
          (value (leftRecurrence T q τ) (distanceFromTarget T q j))
          upper)
      (leftClosedIdentifiesCoefficientEnvelope T q j τ side)
      (iterateAdjacentGeometricDecay O
        (leftRecurrence T q τ) (distanceFromTarget T q j)))

rightShellGeometricDecay :
  ∀ {A : AbsorptionArithmetic}
    {M : OrderedSemiringExtension A}
    {O : ReflexiveOrderExtension A}
    {D : FourierShellDynamics A M} →
  (T : TwoSidedGeometricShellDecay A M O D) →
  ∀ q j τ → sideOf T q j ≡ rightSide T →
  _≤_ A
    (weightedFiveHalvesShell D j (selectedState D q τ))
    (_+_ A (decayCoefficient T q j) (compactGammaEnvelope T q τ))
rightShellGeometricDecay {A} {M} {O} {D} T q j τ side =
  subst
    (λ lower →
      _≤_ A lower
        (_+_ A (decayCoefficient T q j) (compactGammaEnvelope T q τ)))
    (sym (rightShellMeaning T q j τ side))
    (subst
      (λ upper →
        _≤_ A
          (value (rightRecurrence T q τ) (distanceFromTarget T q j))
          upper)
      (rightClosedIdentifiesCoefficientEnvelope T q j τ side)
      (iterateAdjacentGeometricDecay O
        (rightRecurrence T q τ) (distanceFromTarget T q j)))

iteratedTwoSidedFiveHalvesDecay :
  ∀ {A : AbsorptionArithmetic}
    {M : OrderedSemiringExtension A}
    {O : ReflexiveOrderExtension A}
    {D : FourierShellDynamics A M} →
  (T : TwoSidedGeometricShellDecay A M O D) →
  ∀ q j τ →
  _≤_ A
    (weightedFiveHalvesShell D j (selectedState D q τ))
    (_+_ A (decayCoefficient T q j) (compactGammaEnvelope T q τ))
iteratedTwoSidedFiveHalvesDecay T q j τ with sideComplete T q j
... | inj₁ left = leftShellGeometricDecay T q j τ left
... | inj₂ right = rightShellGeometricDecay T q j τ right

summedTwoSidedFiveHalvesEnvelope :
  ∀ {A : AbsorptionArithmetic}
    {M : OrderedSemiringExtension A}
    {O : ReflexiveOrderExtension A}
    {D : FourierShellDynamics A M} →
  (T : TwoSidedGeometricShellDecay A M O D) →
  ∀ q τ →
  _≤_ A (weightedShellSum T q τ) (compactGammaEnvelope T q τ)
summedTwoSidedFiveHalvesEnvelope T =
  sumPointwiseDecay T (iteratedTwoSidedFiveHalvesDecay T)
