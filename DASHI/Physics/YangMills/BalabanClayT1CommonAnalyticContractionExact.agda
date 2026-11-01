module DASHI.Physics.YangMills.BalabanClayT1CommonAnalyticContractionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- T1: one common analytic norm for the Wilson critical map.
--
-- The theorem below does not install contraction as a field.  It derives it
-- from the two model estimates which actually have to be proved:
--
--   ||G f|| <= C_G ||f||,
--   ||N(A)-N(B)|| <= C_N r ||A-B||.
--
-- Consequently the contraction ratio is exactly C_G C_N r.  This is the
-- common quantitative bridge needed by the Picard background construction.
--
-- Order discipline: multiplication is used monotonically only with explicit
-- nonnegative coefficients.  The earlier unrestricted law
-- `prefix * left <= prefix * right` for arbitrary rational `prefix` was false
-- for negative prefixes and has been removed.
------------------------------------------------------------------------

record CommonAnalyticCriticalMap (Index State : Set) : Set₁ where
  field
    zero : State
    subtract : State → State → State
    norm : State → ℚ

    green : Index → State → State
    nonlinear : Index → State → State
    criticalMap : Index → State → State

    radius greenUpper nonlinearSlope contractionRatio : ℚ

    greenUpperNonnegative : 0ℚ ≤ greenUpper
    contractionRatioNonnegative : 0ℚ ≤ contractionRatio

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      left ≤ leftUpper → right ≤ rightUpper →
      left + right ≤ leftUpper + rightUpper
    multiplyMonotoneLeftNonnegative : ∀ prefix {left right} →
      0ℚ ≤ prefix →
      left ≤ right →
      prefix * left ≤ prefix * right

    zeroInBall : norm zero ≤ radius

    criticalMapDifferenceExact : ∀ index left right →
      subtract (criticalMap index left) (criticalMap index right)
      ≡ green index (subtract (nonlinear index left) (nonlinear index right))

    greenBound : ∀ index source →
      norm (green index source) ≤ greenUpper * norm source

    nonlinearLipschitzOnBall : ∀ index left right →
      norm left ≤ radius → norm right ≤ radius →
      norm (subtract (nonlinear index left) (nonlinear index right))
      ≤ (nonlinearSlope * radius) * norm (subtract left right)

    contractionScaleExact : ∀ distanceValue →
      greenUpper * ((nonlinearSlope * radius) * distanceValue)
      ≡ contractionRatio * distanceValue

    triangleFromZero : ∀ index state →
      norm (criticalMap index state)
      ≤ norm (criticalMap index zero)
        + norm (subtract (criticalMap index state) (criticalMap index zero))

    mapAtZeroBudget : ∀ index →
      norm (criticalMap index zero) + contractionRatio * radius ≤ radius

open CommonAnalyticCriticalMap public

InCommonBall :
  ∀ {Index State} → CommonAnalyticCriticalMap Index State → State → Set
InCommonBall dataSet state = norm dataSet state ≤ radius dataSet

criticalMapContraction :
  ∀ {Index State}
    (dataSet : CommonAnalyticCriticalMap Index State)
    index left right →
  InCommonBall dataSet left →
  InCommonBall dataSet right →
  norm dataSet
    (subtract dataSet (criticalMap dataSet index left)
      (criticalMap dataSet index right))
  ≤ contractionRatio dataSet * norm dataSet (subtract dataSet left right)
criticalMapContraction dataSet index left right leftInBall rightInBall =
  subst
    (λ upper →
      norm dataSet
        (subtract dataSet (criticalMap dataSet index left)
          (criticalMap dataSet index right))
      ≤ upper)
    (contractionScaleExact dataSet (norm dataSet (subtract dataSet left right)))
    (transitive dataSet
      (subst
        (λ value →
          norm dataSet value
          ≤ greenUpper dataSet
              * norm dataSet
                  (subtract dataSet (nonlinear dataSet index left)
                    (nonlinear dataSet index right)))
        (sym (criticalMapDifferenceExact dataSet index left right))
        (greenBound dataSet index
          (subtract dataSet (nonlinear dataSet index left)
            (nonlinear dataSet index right))))
      (multiplyMonotoneLeftNonnegative dataSet (greenUpper dataSet)
        (greenUpperNonnegative dataSet)
        (nonlinearLipschitzOnBall dataSet index left right
          leftInBall rightInBall)))

criticalMapPreservesCommonBall :
  ∀ {Index State}
    (dataSet : CommonAnalyticCriticalMap Index State)
    index state →
  InCommonBall dataSet state →
  InCommonBall dataSet (criticalMap dataSet index state)
criticalMapPreservesCommonBall dataSet index state stateInBall =
  transitive dataSet
    (triangleFromZero dataSet index state)
    (transitive dataSet
      (addMonotone dataSet
        (reflexive dataSet (norm dataSet (criticalMap dataSet index (zero dataSet))))
        (criticalMapContraction dataSet index state (zero dataSet)
          stateInBall (zeroInBall dataSet)))
      (transitive dataSet
        (addMonotone dataSet
          (reflexive dataSet (norm dataSet (criticalMap dataSet index (zero dataSet))))
          (multiplyMonotoneLeftNonnegative dataSet
            (contractionRatio dataSet)
            (contractionRatioNonnegative dataSet)
            stateInBall))
        (mapAtZeroBudget dataSet index)))

------------------------------------------------------------------------
-- A single second-jet envelope owns all five P1 Hessian pieces in exactly the
-- same norm and with one total coefficient.  No term may silently use a
-- different radius or order relation.
------------------------------------------------------------------------

record CommonSecondJetEnvelope (Background State : Set) : Set₁ where
  field
    normSq : State → ℚ
    totalRemainder : Background → State → ℚ
    curvature transport chart gauge constraint : Background → State → ℚ

    curvatureUpper transportUpper chartUpper gaugeUpper constraintUpper : ℚ
    totalUpper : ℚ

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      left ≤ leftUpper → right ≤ rightUpper →
      left + right ≤ leftUpper + rightUpper

    totalBelowPieces : ∀ background state →
      totalRemainder background state
      ≤ curvature background state
        + (transport background state
        + (chart background state
        + (gauge background state + constraint background state)))

    curvatureBound : ∀ background state →
      curvature background state ≤ curvatureUpper * normSq state
    transportBound : ∀ background state →
      transport background state ≤ transportUpper * normSq state
    chartBound : ∀ background state →
      chart background state ≤ chartUpper * normSq state
    gaugeBound : ∀ background state →
      gauge background state ≤ gaugeUpper * normSq state
    constraintBound : ∀ background state →
      constraint background state ≤ constraintUpper * normSq state

    totalScaleExact : ∀ radiusValue →
      curvatureUpper * radiusValue
      + (transportUpper * radiusValue
      + (chartUpper * radiusValue
      + (gaugeUpper * radiusValue + constraintUpper * radiusValue)))
      ≡ totalUpper * radiusValue

open CommonSecondJetEnvelope public

commonSecondJetBound :
  ∀ {Background State}
    (dataSet : CommonSecondJetEnvelope Background State)
    background state →
  totalRemainder dataSet background state
  ≤ totalUpper dataSet * normSq dataSet state
commonSecondJetBound dataSet background state =
  subst
    (λ upper → totalRemainder dataSet background state ≤ upper)
    (totalScaleExact dataSet (normSq dataSet state))
    (transitive dataSet
      (totalBelowPieces dataSet background state)
      (addMonotone dataSet
        (curvatureBound dataSet background state)
        (addMonotone dataSet
          (transportBound dataSet background state)
          (addMonotone dataSet
            (chartBound dataSet background state)
            (addMonotone dataSet
              (gaugeBound dataSet background state)
              (constraintBound dataSet background state))))))

commonAnalyticCriticalMapContractionLevel : ProofLevel
commonAnalyticCriticalMapContractionLevel = machineChecked

commonAnalyticCriticalMapSelfMapLevel : ProofLevel
commonAnalyticCriticalMapSelfMapLevel = machineChecked

commonAnalyticNonnegativeMultiplierLevel : ProofLevel
commonAnalyticNonnegativeMultiplierLevel = machineChecked

commonSecondJetFiveTermLevel : ProofLevel
commonSecondJetFiveTermLevel = machineChecked

-- Literal Wilson Green and nonlinear estimates in this exact norm remain the
-- model-specific theorem, rather than being hidden as a preassembled contraction.
t1LiteralWilsonCommonNormInputsLevel : ProofLevel
t1LiteralWilsonCommonNormInputsLevel = conditional
