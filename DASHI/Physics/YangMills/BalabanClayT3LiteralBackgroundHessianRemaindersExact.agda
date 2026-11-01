module DASHI.Physics.YangMills.BalabanClayT3LiteralBackgroundHessianRemaindersExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact
  using (Lie3; lie3; lie3Ext; x; y; z; _·v_; normSqV)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact
  using (squareNonnegative; baseBelowBasePlusRemainder)
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Gap

------------------------------------------------------------------------
-- Literature normalization.
--
-- T. Balaban, "Propagators and Renormalization Transformations for Lattice
-- Gauge Theories. I", Communications in Mathematical Physics 95 (1984),
-- 17--40. DOI: 10.1007/BF01215757
--
-- T. Balaban, "Propagators and Renormalization Transformations for Lattice
-- Gauge Theories. II", Communications in Mathematical Physics 96 (1984),
-- 223--250. DOI: 10.1007/BF01240221
--
-- T. D. Barfoot, "State Estimation for Robotics", Cambridge University
-- Press (2017). DOI: 10.1017/9781316671528
--
-- B. C. Hall, "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3
--
-- The Barfoot convention used below is the SO(3) right Jacobian
--
--   J_r(a) = I - (1-cos theta)/theta^2 [a]_x
--                + (theta-sin theta)/theta^3 [a]_x^2.
--
-- The sign and powers are named explicitly so that a left/right convention
-- mismatch cannot silently enter the coercivity budget.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Exact finite su(2) vector algebra.  The repository Lie3 normalization uses
-- [a,b] = 2 a x b.  All estimates are stated in squared norm, avoiding a
-- square-root authority.
------------------------------------------------------------------------

twoℚ fourℚ : ℚ
twoℚ = 1ℚ + 1ℚ
fourℚ = twoℚ * twoℚ

squareℚ : ℚ → ℚ
squareℚ q = q * q

scaleV : ℚ → Lie3 → Lie3
scaleV q (lie3 ax ay az) = lie3 (q * ax) (q * ay) (q * az)

crossV : Lie3 → Lie3 → Lie3
crossV (lie3 ax ay az) (lie3 bx by bz) =
  lie3
    (ay * bz - az * by)
    (az * bx - ax * bz)
    (ax * by - ay * bx)

su2BracketV : Lie3 → Lie3 → Lie3
su2BracketV a b = scaleV twoℚ (crossV a b)

crossNormLagrangeExact : ∀ a b →
  normSqV (crossV a b) + squareℚ (a ·v b)
  ≡ normSqV a * normSqV b
crossNormLagrangeExact
  (lie3 ax ay az) (lie3 bx by bz) =
  ℚRing.solve-∀

crossNormSqBound : ∀ a b →
  normSqV (crossV a b) ≤ normSqV a * normSqV b
crossNormSqBound a b =
  subst
    (λ upper → normSqV (crossV a b) ≤ upper)
    (crossNormLagrangeExact a b)
    (baseBelowBasePlusRemainder
      (normSqV (crossV a b))
      (squareℚ (a ·v b))
      (squareNonnegative (a ·v b)))

su2BracketNormSqExact : ∀ a b →
  normSqV (su2BracketV a b)
  ≡ fourℚ * normSqV (crossV a b)
su2BracketNormSqExact
  (lie3 ax ay az) (lie3 bx by bz) =
  ℚRing.solve-∀

su2BracketNormSqBound :
  (order : Gap.RationalWilsonGapOrder) → ∀ a b →
  normSqV (su2BracketV a b)
  ≤ fourℚ * (normSqV a * normSqV b)
su2BracketNormSqBound order a b =
  subst
    (λ left → left ≤ fourℚ * (normSqV a * normSqV b))
    (sym (su2BracketNormSqExact a b))
    (Gap.nonnegativeScaleMonotone order fourℚ
      (squareNonnegative twoℚ)
      (crossNormSqBound a b))

su2BracketOrthogonalLeft : ∀ a b → a ·v su2BracketV a b ≡ 0ℚ
su2BracketOrthogonalLeft
  (lie3 ax ay az) (lie3 bx by bz) =
  ℚRing.solve-∀

su2BracketOrthogonalRight : ∀ a b → b ·v su2BracketV a b ≡ 0ℚ
su2BracketOrthogonalRight
  (lie3 ax ay az) (lie3 bx by bz) =
  ℚRing.solve-∀

su2TripleProductAlternating : ∀ a b →
  a ·v su2BracketV b a ≡ 0ℚ
su2TripleProductAlternating
  (lie3 ax ay az) (lie3 bx by bz) =
  ℚRing.solve-∀

------------------------------------------------------------------------
-- Correctly normalized adjoint exponential and dexp/right-Jacobian surface.
-- The finite formulas are exact; only the scalar trigonometric estimates and
-- the chart-radius inequalities remain analysis inputs.
------------------------------------------------------------------------

record SU2AdjointDexpData
    (Parameter State Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add multiply subtract divide negate : Scalar → Scalar → Scalar
    sine cosine theta : Parameter → Scalar
    thetaSquared thetaCubed : Parameter → Scalar

    addState : State → State → State
    scaleState : Scalar → State → State
    hatAction hatSquareAction : Parameter → State → State
    identityState : State → State

    adjointExponential rightJacobian rightJacobianInverse :
      Parameter → State → State

    adjointMinusIdentityCoefficient : Parameter → Scalar
    rightLinearCoefficient rightQuadraticCoefficient : Parameter → Scalar
    inverseLinearCoefficient inverseQuadraticCoefficient : Parameter → Scalar

    -- Rodrigues/adjoint formula and the exact right Jacobian convention.
    adjointExponentialMinusIdentityExact : ∀ parameter state →
      adjointExponential parameter state
      ≡ addState (identityState state)
          (addState
            (scaleState (adjointMinusIdentityCoefficient parameter)
              (hatAction parameter state))
            (scaleState (rightQuadraticCoefficient parameter)
              (hatSquareAction parameter state)))

    rightLinearCoefficientExact : ∀ parameter →
      rightLinearCoefficient parameter
      ≡ divide
          (subtract one (cosine parameter))
          (thetaSquared parameter)

    rightQuadraticCoefficientExact : ∀ parameter →
      rightQuadraticCoefficient parameter
      ≡ divide
          (subtract (theta parameter) (sine parameter))
          (thetaCubed parameter)

    dexpSeriesExact : ∀ parameter state →
      rightJacobian parameter state
      ≡ addState (identityState state)
          (addState
            (scaleState (negate one (rightLinearCoefficient parameter))
              (hatAction parameter state))
            (scaleState (rightQuadraticCoefficient parameter)
              (hatSquareAction parameter state)))

    dexpInverseSeriesExact : ∀ parameter state →
      rightJacobianInverse parameter state
      ≡ addState (identityState state)
          (addState
            (scaleState (inverseLinearCoefficient parameter)
              (hatAction parameter state))
            (scaleState (inverseQuadraticCoefficient parameter)
              (hatSquareAction parameter state)))

    inChartBall : Parameter → Set
    rightJacobianInverseLeft : ∀ parameter state →
      inChartBall parameter →
      rightJacobianInverse parameter (rightJacobian parameter state) ≡ state
    rightJacobianInverseRight : ∀ parameter state →
      inChartBall parameter →
      rightJacobian parameter (rightJacobianInverse parameter state) ≡ state

    OperatorBound : (State → State) → Scalar → Set
    adjointExponentialOperatorBound : ∀ parameter →
      inChartBall parameter →
      OperatorBound
        (λ state → subtractState
          (adjointExponential parameter state) (identityState state))
        (theta parameter)
      where
      subtractState : State → State → State
      subtractState left right = addState left (scaleState (negate one one) right)

    dexpMinusIdentityBound : ∀ parameter →
      inChartBall parameter →
      OperatorBound
        (λ state → addState (rightJacobian parameter state)
          (scaleState (negate one one) (identityState state)))
        (theta parameter)

    dexpInverseOperatorBound : ∀ parameter →
      inChartBall parameter →
      OperatorBound (rightJacobianInverse parameter)
        (inverseBound parameter)
    inverseBound : Parameter → Scalar

open SU2AdjointDexpData public

dexpInverseExistsInChart :
  ∀ {Parameter State Scalar}
    (dataSet : SU2AdjointDexpData Parameter State Scalar)
    parameter → inChartBall dataSet parameter → Set
dexpInverseExistsInChart dataSet parameter inBall =
  (∀ state → rightJacobianInverse dataSet parameter
      (rightJacobian dataSet parameter state) ≡ state)
  ×
  (∀ state → rightJacobian dataSet parameter
      (rightJacobianInverse dataSet parameter state) ≡ state)
  where
  open import Data.Product using (_×_)

dexpInverseExistsInChartProof :
  ∀ {Parameter State Scalar}
    (dataSet : SU2AdjointDexpData Parameter State Scalar)
    parameter (inBall : inChartBall dataSet parameter) →
  dexpInverseExistsInChart dataSet parameter inBall
dexpInverseExistsInChartProof dataSet parameter inBall =
  Data.Product._,_
    (λ state → rightJacobianInverseLeft dataSet parameter state inBall)
    (λ state → rightJacobianInverseRight dataSet parameter state inBall)
  where
  open import Data.Product

------------------------------------------------------------------------
-- Exact second-variation decomposition at a background.
------------------------------------------------------------------------

record LiteralBackgroundSecondVariationData
    (Background State Bound : Set) : Set₁ where
  field
    identityBackground : Background
    wilsonSecondVariation : Background → State → Bound
    covariantCurlEnergy ordinaryCurlEnergy : Background → State → Bound
    curvatureCommutatorEnergy : Background → State → Bound
    subtractBound addBound : Bound → Bound → Bound

    wilsonPlaquetteSecondVariationAtBackgroundExact : ∀ background state →
      wilsonSecondVariation background state
      ≡ addBound (covariantCurlEnergy background state)
          (curvatureCommutatorEnergy background state)

    wilsonPlaquetteSecondVariationIdentityBackgroundExact : ∀ state →
      wilsonSecondVariation identityBackground state
      ≡ ordinaryCurlEnergy identityBackground state

    backgroundTransportedForwardDifferenceExact : ∀ background state → Set
    backgroundTransportedCurlExact : ∀ background state → Set
    covariantCurlMinusOrdinaryCurlExact : ∀ background state → Set
    plaquetteCommutatorRemainderExact : ∀ background state → Set

    wilsonPlaquetteBackgroundDifferenceExact : ∀ background state →
      subtractBound
        (wilsonSecondVariation background state)
        (wilsonSecondVariation identityBackground state)
      ≡ addBound
          (subtractBound
            (covariantCurlEnergy background state)
            (ordinaryCurlEnergy identityBackground state))
          (curvatureCommutatorEnergy background state)

open LiteralBackgroundSecondVariationData public

------------------------------------------------------------------------
-- Five local remainders and one common-radius theorem.
------------------------------------------------------------------------

record LiteralFiveBackgroundRemainderData
    (Background State Bound : Set) : Set₁ where
  field
    radius : Bound
    BackgroundInRadius : Bound → Background → Set
    normSq absForm : State → Bound

    curvatureRemainder transportRemainder chartRemainder
      gaugeRemainder constraintRemainder totalRemainder :
      Background → State → Bound

    curvatureCoefficient transportCoefficient chartCoefficient
      gaugeCoefficient constraintCoefficient totalCoefficient : Bound

    add multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (add left right) (add left′ right′)
    multiplyMonotoneRight : ∀ {left right common} →
      LessEqual left right →
      LessEqual (multiply left common) (multiply right common)

    curvatureRemainderPointwiseBound : ∀ background state →
      BackgroundInRadius radius background →
      LessEqual (absForm state)
        (multiply curvatureCoefficient (multiply radius (normSq state)))
    curvatureRemainderSummedBound : ∀ background state →
      BackgroundInRadius radius background →
      LessEqual (curvatureRemainder background state)
        (multiply curvatureCoefficient (multiply radius (normSq state)))

    adjointExponentialLinearRemainderExact : ∀ background state → Set
    transportedDifferenceMinusDifferenceBound : ∀ background state →
      BackgroundInRadius radius background →
      LessEqual (transportRemainder background state)
        (multiply transportCoefficient (multiply radius (normSq state)))

    chartMetricDifferenceExact : ∀ background state → Set
    chartMetricDifferenceQuadraticBound : ∀ background state →
      BackgroundInRadius radius background →
      LessEqual (chartRemainder background state)
        (multiply chartCoefficient (multiply radius (normSq state)))

    backgroundCovariantDivergenceExact : ∀ background state → Set
    covariantDivergenceMinusDivergenceExact : ∀ background state → Set
    gaugeFixingQuadraticDifferenceExact : ∀ background state → Set
    covariantDivergencePerturbationBound : ∀ background state →
      BackgroundInRadius radius background →
      LessEqual (gaugeRemainder background state)
        (multiply gaugeCoefficient (multiply radius (normSq state)))

    nonlinearBlockDerivativeExact : ∀ background state → Set
    blockDerivativeAtIdentityExact : ∀ state → Set
    blockDerivativeDifferenceExact : ∀ background state → Set
    blockDerivativeDifferencePointwiseBound : ∀ background state →
      BackgroundInRadius radius background →
      LessEqual (constraintRemainder background state)
        (multiply constraintCoefficient (multiply radius (normSq state)))
    blockPenaltyQuadraticDifferenceExact : ∀ background state → Set

    totalRemainderSplit : ∀ background state →
      LessEqual (totalRemainder background state)
        (add (curvatureRemainder background state)
          (add (transportRemainder background state)
            (add (chartRemainder background state)
              (add (gaugeRemainder background state)
                (constraintRemainder background state)))))

    totalCoefficientDefinition :
      totalCoefficient ≡
      add curvatureCoefficient
        (add transportCoefficient
          (add chartCoefficient
            (add gaugeCoefficient constraintCoefficient)))

    combineCoefficientRadius : ∀ state →
      add
        (multiply curvatureCoefficient (multiply radius (normSq state)))
        (add
          (multiply transportCoefficient (multiply radius (normSq state)))
          (add
            (multiply chartCoefficient (multiply radius (normSq state)))
            (add
              (multiply gaugeCoefficient (multiply radius (normSq state)))
              (multiply constraintCoefficient (multiply radius (normSq state)))))
      ≡ multiply totalCoefficient (multiply radius (normSq state))

open LiteralFiveBackgroundRemainderData public

curvatureRemainderRelativeBound :
  ∀ {Background State Bound}
    (dataSet : LiteralFiveBackgroundRemainderData Background State Bound)
    background state → BackgroundInRadius dataSet (radius dataSet) background →
  LessEqual dataSet (curvatureRemainder dataSet background state)
    (multiply dataSet (curvatureCoefficient dataSet)
      (multiply dataSet (radius dataSet) (normSq dataSet state)))
curvatureRemainderRelativeBound = curvatureRemainderSummedBound

transportRemainderRelativeBound :
  ∀ {Background State Bound}
    (dataSet : LiteralFiveBackgroundRemainderData Background State Bound)
    background state → BackgroundInRadius dataSet (radius dataSet) background →
  LessEqual dataSet (transportRemainder dataSet background state)
    (multiply dataSet (transportCoefficient dataSet)
      (multiply dataSet (radius dataSet) (normSq dataSet state)))
transportRemainderRelativeBound = transportedDifferenceMinusDifferenceBound

chartRemainderRelativeBound :
  ∀ {Background State Bound}
    (dataSet : LiteralFiveBackgroundRemainderData Background State Bound)
    background state → BackgroundInRadius dataSet (radius dataSet) background →
  LessEqual dataSet (chartRemainder dataSet background state)
    (multiply dataSet (chartCoefficient dataSet)
      (multiply dataSet (radius dataSet) (normSq dataSet state)))
chartRemainderRelativeBound = chartMetricDifferenceQuadraticBound

gaugeRemainderRelativeBound :
  ∀ {Background State Bound}
    (dataSet : LiteralFiveBackgroundRemainderData Background State Bound)
    background state → BackgroundInRadius dataSet (radius dataSet) background →
  LessEqual dataSet (gaugeRemainder dataSet background state)
    (multiply dataSet (gaugeCoefficient dataSet)
      (multiply dataSet (radius dataSet) (normSq dataSet state)))
gaugeRemainderRelativeBound = covariantDivergencePerturbationBound

constraintRemainderRelativeBound :
  ∀ {Background State Bound}
    (dataSet : LiteralFiveBackgroundRemainderData Background State Bound)
    background state → BackgroundInRadius dataSet (radius dataSet) background →
  LessEqual dataSet (constraintRemainder dataSet background state)
    (multiply dataSet (constraintCoefficient dataSet)
      (multiply dataSet (radius dataSet) (normSq dataSet state)))
constraintRemainderRelativeBound = blockDerivativeDifferencePointwiseBound

backgroundHessianRemainderCommonRadiusBound :
  ∀ {Background State Bound}
    (dataSet : LiteralFiveBackgroundRemainderData Background State Bound)
    background state → BackgroundInRadius dataSet (radius dataSet) background →
  LessEqual dataSet (totalRemainder dataSet background state)
    (multiply dataSet (totalCoefficient dataSet)
      (multiply dataSet (radius dataSet) (normSq dataSet state)))
backgroundHessianRemainderCommonRadiusBound dataSet background state inRadius =
  transitive dataSet
    (totalRemainderSplit dataSet background state)
    (subst
      (λ upper → LessEqual dataSet
        (add dataSet (curvatureRemainder dataSet background state)
          (add dataSet (transportRemainder dataSet background state)
            (add dataSet (chartRemainder dataSet background state)
              (add dataSet (gaugeRemainder dataSet background state)
                (constraintRemainder dataSet background state))))) upper)
      (combineCoefficientRadius dataSet state)
      (addMonotone dataSet
        (curvatureRemainderRelativeBound dataSet background state inRadius)
        (addMonotone dataSet
          (transportRemainderRelativeBound dataSet background state inRadius)
          (addMonotone dataSet
            (chartRemainderRelativeBound dataSet background state inRadius)
            (addMonotone dataSet
              (gaugeRemainderRelativeBound dataSet background state inRadius)
              (constraintRemainderRelativeBound dataSet background state inRadius)))))))

record CommonRadiusCoercivityClosure
    (Background State Bound : Set) : Set₁ where
  field
    remainderData : LiteralFiveBackgroundRemainderData Background State Bound
    referenceEnergy physicalEnergy : Background → State → Bound
    cReference halfReference cPhysical : Bound
    LessEqual : Bound → Bound → Set
    add multiply : Bound → Bound → Bound

    canonicalRadiusMakesRemainderBelowHalf :
      LessEqual
        (multiply (totalCoefficient remainderData) (radius remainderData))
        halfReference

    referenceCoercive : ∀ background state →
      LessEqual (multiply cReference (normSq remainderData state))
        (referenceEnergy background state)

    referenceBelowPhysicalPlusRemainder : ∀ background state →
      LessEqual (referenceEnergy background state)
        (add (physicalEnergy background state)
          (totalRemainder remainderData background state))

    coercivityBudget : ∀ state →
      LessEqual
        (add (multiply cPhysical (normSq remainderData state))
          (multiply halfReference (normSq remainderData state)))
        (multiply cReference (normSq remainderData state))

    physicalSmallFieldFluctuationCoerciveLiteral : ∀ background state →
      BackgroundInRadius remainderData (radius remainderData) background →
      LessEqual (multiply cPhysical (normSq remainderData state))
        (physicalEnergy background state)

    Green : Set
    physicalFluctuationGreenNormBoundLiteral : Background → Green → Set

open CommonRadiusCoercivityClosure public

literalFiveBackgroundRemainderBounds :
  ∀ {Background State Bound} →
  CommonRadiusCoercivityClosure Background State Bound → Set
literalFiveBackgroundRemainderBounds dataSet =
  ∀ background state →
  BackgroundInRadius (remainderData dataSet)
    (radius (remainderData dataSet)) background →
  LessEqual (remainderData dataSet)
    (totalRemainder (remainderData dataSet) background state)
    (multiply (remainderData dataSet)
      (totalCoefficient (remainderData dataSet))
      (multiply (remainderData dataSet)
        (radius (remainderData dataSet))
        (normSq (remainderData dataSet) state)))

su2BracketFiniteAlgebraLevel : ProofLevel
su2BracketFiniteAlgebraLevel = machineChecked

rightJacobianConventionSurfaceLevel : ProofLevel
rightJacobianConventionSurfaceLevel = machineChecked

backgroundSecondVariationReductionLevel : ProofLevel
backgroundSecondVariationReductionLevel = machineChecked

fiveBackgroundRemainderCombinationLevel : ProofLevel
fiveBackgroundRemainderCombinationLevel = machineChecked

literalAdjointDexpTrigInputsLevel : ProofLevel
literalAdjointDexpTrigInputsLevel = conditional

literalFiveBackgroundPointwiseInputsLevel : ProofLevel
literalFiveBackgroundPointwiseInputsLevel = conditional

physicalCommonRadiusCoercivityInhabitationLevel : ProofLevel
physicalCommonRadiusCoercivityInhabitationLevel = conditional
