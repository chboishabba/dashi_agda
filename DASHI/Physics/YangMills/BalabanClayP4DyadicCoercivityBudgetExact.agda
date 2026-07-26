module DASHI.Physics.YangMills.BalabanClayP4DyadicCoercivityBudgetExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact using
  ( halfPower
  ; halfPowerNonnegative
  ; traceShellPartialSum
  ; traceShellGeometricIdentity
  )

------------------------------------------------------------------------
-- An explicit summable loss schedule.
--
-- Starting from c0 = 1/32, assign loss_k = (1/128) 2^{-k}.  The exact finite
-- identity says that the consumed loss plus its geometric tail is 1/64.  Hence
-- every finite number of RG steps retains at least 1/64 coercivity.
------------------------------------------------------------------------

oneThirtySecond oneSixtyFourth oneOneTwentyEighth : ℚ
oneThirtySecond = + 1 / 32
oneSixtyFourth = + 1 / 64
oneOneTwentyEighth = + 1 / 128

coercivityLoss : Nat → ℚ
coercivityLoss scale = oneOneTwentyEighth * halfPower scale

lossPartialSum : Nat → ℚ
lossPartialSum zero = 0ℚ
lossPartialSum (suc scale) =
  lossPartialSum scale + coercivityLoss scale

lossPartialSumMatchesGeometric : ∀ depth →
  lossPartialSum depth
  ≡ oneOneTwentyEighth * traceShellPartialSum depth
lossPartialSumMatchesGeometric zero = ℚRing.solve-∀
lossPartialSumMatchesGeometric (suc depth)
  rewrite lossPartialSumMatchesGeometric depth =
  ℚRing.solve-∀
    (traceShellPartialSum depth)
    (halfPower depth)

lossBudgetIdentity : ∀ depth →
  lossPartialSum depth
    + oneSixtyFourth * halfPower depth
  ≡ oneSixtyFourth
lossBudgetIdentity depth =
  trans
    (cong
      (λ partial → partial + oneSixtyFourth * halfPower depth)
      (lossPartialSumMatchesGeometric depth))
    (trans
      (ℚRing.solve-∀
        (traceShellPartialSum depth) (halfPower depth))
      (cong (oneOneTwentyEighth *_)
        (traceShellGeometricIdentity depth)))

oneSixtyFourthTimesHalfPowerNonnegative : ∀ depth →
  0ℚ ≤ oneSixtyFourth * halfPower depth
oneSixtyFourthTimesHalfPowerNonnegative depth =
  let
    coefficientNonnegativeProof : 0ℚ ≤ oneSixtyFourth
    coefficientNonnegativeProof =
      let
        instance
          coefficientNonnegative : NonNegative oneSixtyFourth
          coefficientNonnegative = ℚP.normalize-nonNeg 1 64
      in
      ℚP.nonNegative⁻¹ oneSixtyFourth

    instance
      coefficientNonnegative : NonNegative oneSixtyFourth
      coefficientNonnegative = nonNegative coefficientNonnegativeProof

      powerNonnegative : NonNegative (halfPower depth)
      powerNonnegative = nonNegative (halfPowerNonnegative depth)

      productNonnegative : NonNegative (oneSixtyFourth * halfPower depth)
      productNonnegative =
        ℚP.nonNeg*nonNeg⇒nonNeg oneSixtyFourth (halfPower depth)
  in
  ℚP.nonNegative⁻¹ (oneSixtyFourth * halfPower depth)

lossPartialSumBelowOneSixtyFourth : ∀ depth →
  lossPartialSum depth ≤ oneSixtyFourth
lossPartialSumBelowOneSixtyFourth depth =
  subst
    (λ upper → lossPartialSum depth ≤ upper)
    (lossBudgetIdentity depth)
    (baseBelowBasePlusRemainder
      (lossPartialSum depth)
      (oneSixtyFourth * halfPower depth)
      (oneSixtyFourthTimesHalfPowerNonnegative depth))

oneSixtyFourthDouble :
  oneSixtyFourth + oneSixtyFourth ≡ oneThirtySecond
oneSixtyFourthDouble = ℚRing.solve-∀

------------------------------------------------------------------------
-- Quantitative recurrence theorem.
------------------------------------------------------------------------

record DyadicCoercivityRecurrence : Set₁ where
  field
    coercivityAt : Nat → ℚ

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      left ≤ leftUpper → right ≤ rightUpper →
      left + right ≤ leftUpper + rightUpper
    addRightCancel : ∀ {left right common} →
      left + common ≤ right + common → left ≤ right

    initialCoercivity : oneThirtySecond ≤ coercivityAt zero
    oneStepLossBound : ∀ scale →
      coercivityAt scale
      ≤ coercivityAt (suc scale) + coercivityLoss scale

open DyadicCoercivityRecurrence public

initialBelowCoercivityPlusConsumedLoss :
  (dataSet : DyadicCoercivityRecurrence) → ∀ depth →
  oneThirtySecond
  ≤ coercivityAt dataSet depth + lossPartialSum depth
initialBelowCoercivityPlusConsumedLoss dataSet zero =
  subst
    (λ right → oneThirtySecond ≤ right)
    (sym (ℚRing.solve-∀ (coercivityAt dataSet zero)))
    (initialCoercivity dataSet)
initialBelowCoercivityPlusConsumedLoss dataSet (suc depth) =
  transitive dataSet
    (initialBelowCoercivityPlusConsumedLoss dataSet depth)
    (subst
      (λ right →
        coercivityAt dataSet depth + lossPartialSum depth ≤ right)
      (ℚRing.solve-∀
        (coercivityAt dataSet (suc depth))
        (coercivityLoss depth)
        (lossPartialSum depth))
      (addMonotone dataSet
        (oneStepLossBound dataSet depth)
        (reflexive dataSet (lossPartialSum depth))))

uniformOneSixtyFourthCoercivity :
  (dataSet : DyadicCoercivityRecurrence) → ∀ depth →
  oneSixtyFourth ≤ coercivityAt dataSet depth
uniformOneSixtyFourthCoercivity dataSet depth =
  addRightCancel dataSet
    (transitive dataSet
      (subst
        (λ left →
          left ≤ coercivityAt dataSet depth + lossPartialSum depth)
        oneSixtyFourthDouble
        (initialBelowCoercivityPlusConsumedLoss dataSet depth))
      (addMonotone dataSet
        (reflexive dataSet (coercivityAt dataSet depth))
        (lossPartialSumBelowOneSixtyFourth depth)))

record UniformAllScaleCoercivityCertificate : Set₁ where
  field
    recurrence : DyadicCoercivityRecurrence
    uniformPositiveLowerBound : ∀ depth →
      oneSixtyFourth ≤ coercivityAt recurrence depth
    uniformPositiveLowerBound =
      uniformOneSixtyFourthCoercivity recurrence

open UniformAllScaleCoercivityCertificate public

dyadicLossFiniteIdentityLevel : ProofLevel
dyadicLossFiniteIdentityLevel = machineChecked

dyadicLossUniformBoundLevel : ProofLevel
dyadicLossUniformBoundLevel = machineChecked

allScaleCoercivityRecurrenceLevel : ProofLevel
allScaleCoercivityRecurrenceLevel = machineChecked

physicalOneStepLossEstimateLevel : ProofLevel
physicalOneStepLossEstimateLevel = conditional
