module DASHI.Physics.YangMills.BalabanClayP1BackgroundStabilityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- P1A: the actual minimizing background, rather than an arbitrary index.
------------------------------------------------------------------------

record RegularBackgroundConstruction
    (CoarseField FineField Background Bound : Set) : Set₁ where
  field
    blockMap : Background → CoarseField
    backgroundOf : CoarseField → Background
    reconstructFine : Background → FineField

    zeroBound : Bound
    actionFirstVariation : Background → FineField → Bound
    ConstraintTangent : Background → FineField → Set
    GaugeFixedBackground CandidateStationary : Background → Set

    backgroundSatisfiesConstraint : ∀ coarse →
      blockMap (backgroundOf coarse) ≡ coarse

    backgroundGaugeFixed : ∀ coarse →
      GaugeFixedBackground (backgroundOf coarse)

    backgroundStationary : ∀ coarse tangent →
      ConstraintTangent (backgroundOf coarse) tangent →
      actionFirstVariation (backgroundOf coarse) tangent ≡ zeroBound

    backgroundCandidateStationary : ∀ coarse →
      CandidateStationary (backgroundOf coarse)

    BackgroundEquivalent : Background → Background → Set
    minimizerUniqueModuloGauge : ∀ coarse candidate →
      blockMap candidate ≡ coarse →
      GaugeFixedBackground candidate →
      CandidateStationary candidate →
      BackgroundEquivalent candidate (backgroundOf coarse)

    regularitySize : Background → Bound
    coarseSmallness : CoarseField → Bound
    regularityConstant : Bound
    scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    backgroundRegularity : ∀ coarse →
      LessEqual
        (regularitySize (backgroundOf coarse))
        (scale regularityConstant (coarseSmallness coarse))

open RegularBackgroundConstruction public

------------------------------------------------------------------------
-- P1B--P1C: literal Hessian difference and the five quantitative pieces.
------------------------------------------------------------------------

record FiveTermBackgroundHessianData
    (Background State Bound : Set) : Set₁ where
  field
    referenceHessian backgroundHessian hessianRemainder :
      Background → State → State
    addState : State → State → State
    inner : State → State → Bound
    Absolute : Bound → Bound
    normSq : State → Bound

    backgroundHessianExact : ∀ background state →
      backgroundHessian background state
      ≡ addState
          (referenceHessian background state)
          (hessianRemainder background state)

    perturbationMagnitude : Background → State → Bound
    perturbationMagnitudeExact : ∀ background state →
      perturbationMagnitude background state
      ≡ Absolute (inner state (hessianRemainder background state))

    curvaturePart transportPart chartPart gaugePart constraintPart :
      Background → State → Bound

    curvatureUpper transportUpper chartUpper gaugeUpper constraintUpper : Bound

    add scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    perturbationBelowFiveTerms : ∀ background state →
      LessEqual (perturbationMagnitude background state)
        (add (curvaturePart background state)
          (add (transportPart background state)
            (add (chartPart background state)
              (add (gaugePart background state)
                (constraintPart background state)))))

    curvatureBound : ∀ background state →
      LessEqual (curvaturePart background state)
        (scale curvatureUpper (normSq state))
    transportBound : ∀ background state →
      LessEqual (transportPart background state)
        (scale transportUpper (normSq state))
    chartBound : ∀ background state →
      LessEqual (chartPart background state)
        (scale chartUpper (normSq state))
    gaugeBound : ∀ background state →
      LessEqual (gaugePart background state)
        (scale gaugeUpper (normSq state))
    constraintBound : ∀ background state →
      LessEqual (constraintPart background state)
        (scale constraintUpper (normSq state))

    combineScaledFive : ∀ radius →
      add (scale curvatureUpper radius)
        (add (scale transportUpper radius)
          (add (scale chartUpper radius)
            (add (scale gaugeUpper radius)
              (scale constraintUpper radius))))
      ≡ scale
          (add curvatureUpper
            (add transportUpper
              (add chartUpper (add gaugeUpper constraintUpper))))
          radius

open FiveTermBackgroundHessianData public

backgroundConstant :
  ∀ {Background State Bound} →
  FiveTermBackgroundHessianData Background State Bound → Bound
backgroundConstant dataSet =
  add dataSet (curvatureUpper dataSet)
    (add dataSet (transportUpper dataSet)
      (add dataSet (chartUpper dataSet)
        (add dataSet (gaugeUpper dataSet) (constraintUpper dataSet))))

backgroundRelativeFormSmallness :
  ∀ {Background State Bound}
    (dataSet : FiveTermBackgroundHessianData Background State Bound)
    background state →
  LessEqual dataSet
    (perturbationMagnitude dataSet background state)
    (scale dataSet (backgroundConstant dataSet) (normSq dataSet state))
backgroundRelativeFormSmallness dataSet background state =
  subst
    (λ right →
      LessEqual dataSet
        (perturbationMagnitude dataSet background state) right)
    (combineScaledFive dataSet (normSq dataSet state))
    (transitive dataSet
      (perturbationBelowFiveTerms dataSet background state)
      (addMonotone dataSet
        (curvatureBound dataSet background state)
        (addMonotone dataSet
          (transportBound dataSet background state)
          (addMonotone dataSet
            (chartBound dataSet background state)
            (addMonotone dataSet
              (gaugeBound dataSet background state)
              (constraintBound dataSet background state))))))

------------------------------------------------------------------------
-- P1D: exact 1/16 -> 1/32 coercivity budget over ℚ.
------------------------------------------------------------------------

oneSixteenth oneThirtySecond : ℚ
oneSixteenth = + 1 / 16
oneThirtySecond = + 1 / 32

oneThirtySecondSplit : ∀ radius →
  oneThirtySecond * radius + oneThirtySecond * radius
  ≡ oneSixteenth * radius
oneThirtySecondSplit = ℚRing.solve-∀

record BackgroundCoercivityBudget
    (Background State : Set) : Set₁ where
  field
    referenceEnergy fullEnergy perturbationPenalty : Background → State → ℚ
    normSq : State → ℚ

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      left ≤ leftUpper → right ≤ rightUpper →
      left + right ≤ leftUpper + rightUpper
    addRightCancel : ∀ {left right common} →
      left + common ≤ right + common → left ≤ right

    referenceCoercive : ∀ background state →
      oneSixteenth * normSq state ≤ referenceEnergy background state

    referenceBelowFullPlusPenalty : ∀ background state →
      referenceEnergy background state
      ≤ fullEnergy background state + perturbationPenalty background state

    perturbationFitsHalfMargin : ∀ background state →
      perturbationPenalty background state
      ≤ oneThirtySecond * normSq state

open BackgroundCoercivityBudget public

smallBackgroundOneThirtySecondCoercivity :
  ∀ {Background State}
    (dataSet : BackgroundCoercivityBudget Background State)
    background state →
  oneThirtySecond * normSq dataSet state
  ≤ fullEnergy dataSet background state
smallBackgroundOneThirtySecondCoercivity dataSet background state =
  addRightCancel dataSet
    (transitive dataSet
      (subst
        (λ right →
          oneThirtySecond * normSq dataSet state
            + perturbationPenalty dataSet background state
          ≤ right)
        (oneThirtySecondSplit (normSq dataSet state))
        (addMonotone dataSet
          (reflexive dataSet (oneThirtySecond * normSq dataSet state))
          (perturbationFitsHalfMargin dataSet background state)))
      (transitive dataSet
        (referenceCoercive dataSet background state)
        (referenceBelowFullPlusPenalty dataSet background state)))

------------------------------------------------------------------------
-- Complete P1 certificate.  Its producer fields are intentionally explicit:
-- the theorem above closes the budget, but it does not pretend to construct the
-- nonlinear minimizing background or prove the five model-specific estimates.
------------------------------------------------------------------------

record PhysicalP1BackgroundCertificate
    (CoarseField FineField Background State Bound : Set) : Set₁ where
  field
    backgroundConstruction :
      RegularBackgroundConstruction CoarseField FineField Background Bound
    fiveTermHessian : FiveTermBackgroundHessianData Background State Bound
    rationalCoercivityBudget : BackgroundCoercivityBudget Background State

    relativeFormBound : ∀ background state →
      LessEqual fiveTermHessian
        (perturbationMagnitude fiveTermHessian background state)
        (scale fiveTermHessian
          (backgroundConstant fiveTermHessian)
          (normSq fiveTermHessian state))
    relativeFormBound = backgroundRelativeFormSmallness fiveTermHessian

    oneThirtySecondCoercivity : ∀ background state →
      oneThirtySecond * BackgroundCoercivityBudget.normSq
        rationalCoercivityBudget state
      ≤ fullEnergy rationalCoercivityBudget background state
    oneThirtySecondCoercivity =
      smallBackgroundOneThirtySecondCoercivity rationalCoercivityBudget

open PhysicalP1BackgroundCertificate public

p1LiteralHessianDifferenceSurfaceLevel : ProofLevel
p1LiteralHessianDifferenceSurfaceLevel = machineChecked

p1FiveTermAssemblyLevel : ProofLevel
p1FiveTermAssemblyLevel = machineChecked

p1OneThirtySecondBudgetLevel : ProofLevel
p1OneThirtySecondBudgetLevel = machineChecked

p1MinimizingBackgroundProducerLevel : ProofLevel
p1MinimizingBackgroundProducerLevel = conditional

p1FiveUniformComponentEstimatesLevel : ProofLevel
p1FiveUniformComponentEstimatesLevel = conditional
