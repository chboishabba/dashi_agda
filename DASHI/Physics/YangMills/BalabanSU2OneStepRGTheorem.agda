module DASHI.Physics.YangMills.BalabanSU2OneStepRGTheorem where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)

record RGCoordinates {g k e : Level}
  (Coupling : Set g) (Irrelevant : Set k) (Vacuum : Set e) : Set (g ⊔ k ⊔ e) where
  constructor rgCoordinates
  field
    coupling : Coupling
    irrelevant : Irrelevant
    vacuum : Vacuum
open RGCoordinates public

record OneStepRGTheorem
  {g k e a s : Level}
  (Coupling : Set g)
  (Irrelevant : Set k)
  (Vacuum : Set e)
  (EffectiveAction : Set a)
  (Scalar : Set s) : Set (lsuc (g ⊔ k ⊔ e ⊔ a ⊔ s)) where
  field
    input output : RGCoordinates Coupling Irrelevant Vacuum
    effectiveAction : EffectiveAction
    reconstructedAction : RGCoordinates Coupling Irrelevant Vacuum → EffectiveAction
    effectiveActionExactDecomposition :
      effectiveAction ≡ reconstructedAction output

    betaCoefficient : Coupling → Irrelevant → Scalar
    marginalCoefficient : EffectiveAction → Scalar
    marginalCoefficientExtraction :
      marginalCoefficient effectiveAction
        ≡ betaCoefficient (coupling input) (irrelevant input)

    wardRelevantPart : EffectiveAction → EffectiveAction
    marginalCounterterm : Scalar → EffectiveAction
    zeroAction : EffectiveAction
    wardCancellation :
      wardRelevantPart effectiveAction
        ≡ marginalCounterterm (marginalCoefficient effectiveAction)

    irrelevantNorm : Irrelevant → Scalar
    couplingRemainder : Coupling → Irrelevant → Scalar
    irrelevantRemainder : Coupling → Irrelevant → Irrelevant

    CouplingRemainderBound : Coupling → Irrelevant → Scalar → Set s
    IrrelevantRemainderBound : Coupling → Irrelevant → Irrelevant → Set s
    irrelevantRemainderBound :
      CouplingRemainderBound
        (coupling input) (irrelevant input)
        (couplingRemainder (coupling input) (irrelevant input))
    irrelevantUpdateBound :
      IrrelevantRemainderBound
        (coupling input) (irrelevant input)
        (irrelevantRemainder (coupling input) (irrelevant input))

    couplingStep : Coupling → Scalar → Coupling
    irrelevantLinearStep : Irrelevant → Irrelevant
    irrelevantAdd : Irrelevant → Irrelevant → Irrelevant

    oneStepCouplingRecursion :
      coupling output
        ≡ couplingStep (coupling input)
            (couplingRemainder (coupling input) (irrelevant input))

    oneStepIrrelevantContraction :
      irrelevant output
        ≡ irrelevantAdd
            (irrelevantLinearStep (irrelevant input))
            (irrelevantRemainder (coupling input) (irrelevant input))

    HistoryDistance : Irrelevant → Irrelevant → Scalar
    BetaDifferenceBound : Scalar → Scalar → Set s
    historyLipschitz :
      ∀ left right →
      BetaDifferenceBound
        (betaCoefficient (coupling input) left)
        (HistoryDistance left right)
open OneStepRGTheorem public

assembleOneStepRGTheorem :
  ∀ {g k e a s}
  {Coupling : Set g} {Irrelevant : Set k} {Vacuum : Set e}
  {EffectiveAction : Set a} {Scalar : Set s} →
  OneStepRGTheorem Coupling Irrelevant Vacuum EffectiveAction Scalar →
  OneStepRGTheorem Coupling Irrelevant Vacuum EffectiveAction Scalar
assembleOneStepRGTheorem theorem = theorem

record OrderedLipschitzSocket {s : Level} (Scalar : Set s) : Set (lsuc s) where
  field
    _≤_ : Scalar → Scalar → Set s
    multiply : Scalar → Scalar → Scalar
    transitive : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    multiplyMonotoneLeft : ∀ constant {a b} → a ≤ b →
      multiply constant a ≤ multiply constant b
open OrderedLipschitzSocket public

-- If beta is C-Lipschitz in the irrelevant coordinate and one RG step contracts
-- that coordinate by q, then the history sensitivity after the step is Cq times
-- the previous distance.  This is the algebraic mechanism by which a contracting
-- K_j lane makes dependence on earlier RG history summable.
betaHistoryStabilityAfterContraction :
  ∀ {k s} {Irrelevant : Set k} {Scalar : Set s}
  (order : OrderedLipschitzSocket Scalar)
  (beta : Irrelevant → Scalar)
  (betaDifference distance : Irrelevant → Irrelevant → Scalar)
  (step : Irrelevant → Irrelevant)
  (lipschitzConstant contractionFactor : Scalar) →
  (∀ left right →
    _≤_ order (betaDifference left right)
      (multiply order lipschitzConstant (distance left right))) →
  (∀ left right →
    _≤_ order (distance (step left) (step right))
      (multiply order contractionFactor (distance left right))) →
  ∀ left right →
  _≤_ order (betaDifference (step left) (step right))
    (multiply order lipschitzConstant
      (multiply order contractionFactor (distance left right)))
betaHistoryStabilityAfterContraction
  order beta betaDifference distance step
  lipschitzConstant contractionFactor
  betaLipschitz stepContractive left right =
  transitive order
    (betaLipschitz (step left) (step right))
    (multiplyMonotoneLeft order lipschitzConstant
      (stepContractive left right))
