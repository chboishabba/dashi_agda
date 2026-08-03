module DASHI.Physics.YangMills.BalabanClayT3SchurWardBetaExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; _/_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact using
  (half)

------------------------------------------------------------------------
-- T3A: exact Schur completion in the one-dimensional block model.
------------------------------------------------------------------------

scalarFluctuationMinimizer : ℚ → ℚ → ℚ → ℚ
scalarFluctuationMinimizer mixed inverseFluctuation coarse =
  - (inverseFluctuation * mixed * coarse)

scalarBlockEnergy : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
scalarBlockEnergy coarseHessian mixed fluctuationHessian coarse fluctuation =
  coarseHessian * coarse * coarse
  + (+ 2 / 1) * mixed * coarse * fluctuation
  + fluctuationHessian * fluctuation * fluctuation

scalarSchurHessian : ℚ → ℚ → ℚ → ℚ
scalarSchurHessian coarseHessian mixed inverseFluctuation =
  coarseHessian - mixed * inverseFluctuation * mixed

scalarSchurDefectIdentity : ∀ coarseHessian mixed fluctuationHessian
    inverseFluctuation coarse →
  scalarBlockEnergy coarseHessian mixed fluctuationHessian coarse
    (scalarFluctuationMinimizer mixed inverseFluctuation coarse)
  ≡ scalarSchurHessian coarseHessian mixed inverseFluctuation * coarse * coarse
    + (fluctuationHessian * inverseFluctuation - 1ℚ)
      * (inverseFluctuation * mixed * mixed * coarse * coarse)
scalarSchurDefectIdentity = ℚRing.solve-∀

scalarSchurEnergyExact : ∀ coarseHessian mixed fluctuationHessian
    inverseFluctuation coarse →
  fluctuationHessian * inverseFluctuation ≡ 1ℚ →
  scalarBlockEnergy coarseHessian mixed fluctuationHessian coarse
    (scalarFluctuationMinimizer mixed inverseFluctuation coarse)
  ≡ scalarSchurHessian coarseHessian mixed inverseFluctuation * coarse * coarse
scalarSchurEnergyExact coarseHessian mixed fluctuationHessian
    inverseFluctuation coarse inverseProduct =
  trans
    (scalarSchurDefectIdentity coarseHessian mixed fluctuationHessian
      inverseFluctuation coarse)
    (subst
      (λ product →
        scalarSchurHessian coarseHessian mixed inverseFluctuation * coarse * coarse
        + (product - 1ℚ)
          * (inverseFluctuation * mixed * mixed * coarse * coarse)
        ≡ scalarSchurHessian coarseHessian mixed inverseFluctuation * coarse * coarse)
      (sym inverseProduct)
      (ℚRing.solve-∀))

------------------------------------------------------------------------
-- T3B/T4A: gauge invariance is produced from exact reindexing of the actual
-- constrained integral.  It is not postulated on the resulting action.
------------------------------------------------------------------------

record ExactGaugeReindexedIntegral
    (Gauge Fine Coarse Weight Scalar : Set) : Set₁ where
  field
    transformFine : Gauge → Fine → Fine
    transformCoarse : Gauge → Coarse → Coarse
    constrainedIntegral : (Fine → Weight) → Coarse → Scalar

    reindexGauge : ∀ gauge weight coarse →
      constrainedIntegral weight (transformCoarse gauge coarse)
      ≡ constrainedIntegral (λ field → weight (transformFine gauge field)) coarse

    boltzmannWeight : Fine → Weight
    boltzmannGaugeInvariant : ∀ gauge field →
      boltzmannWeight (transformFine gauge field) ≡ boltzmannWeight field

    integralCongruent : ∀ left right coarse →
      (∀ field → left field ≡ right field) →
      constrainedIntegral left coarse ≡ constrainedIntegral right coarse

open ExactGaugeReindexedIntegral public

fluctuationIntegralGaugeInvariant :
  ∀ {Gauge Fine Coarse Weight Scalar}
    (dataSet : ExactGaugeReindexedIntegral Gauge Fine Coarse Weight Scalar)
    gauge coarse →
  constrainedIntegral dataSet (boltzmannWeight dataSet)
    (transformCoarse dataSet gauge coarse)
  ≡ constrainedIntegral dataSet (boltzmannWeight dataSet) coarse
fluctuationIntegralGaugeInvariant dataSet gauge coarse =
  trans
    (reindexGauge dataSet gauge (boltzmannWeight dataSet) coarse)
    (integralCongruent dataSet
      (λ field → boltzmannWeight dataSet (transformFine dataSet gauge field))
      (boltzmannWeight dataSet)
      coarse
      (boltzmannGaugeInvariant dataSet gauge))

record WardPreservingLocalization
    (Gauge EffectiveAction LocalTerm : Set) : Set₁ where
  field
    transformAction : Gauge → EffectiveAction → EffectiveAction
    transformLocal : Gauge → LocalTerm → LocalTerm
    localize : EffectiveAction → LocalTerm
    localizationEquivariant : ∀ gauge action →
      localize (transformAction gauge action)
      ≡ transformLocal gauge (localize action)

open WardPreservingLocalization public

localizationPreservesWardIdentity :
  ∀ {Gauge EffectiveAction LocalTerm}
    (dataSet : WardPreservingLocalization Gauge EffectiveAction LocalTerm)
    gauge action →
  localize dataSet (transformAction dataSet gauge action)
  ≡ transformLocal dataSet gauge (localize dataSet action)
localizationPreservesWardIdentity = localizationEquivariant

------------------------------------------------------------------------
-- T4B: a genuinely quartic remainder is summable.
------------------------------------------------------------------------

quarter fourThirds : ℚ
quarter = + 1 / 4
fourThirds = + 4 / 3

couplingSqEnvelope : Nat → ℚ
couplingSqEnvelope zero = 1ℚ
couplingSqEnvelope (suc depth) = half * couplingSqEnvelope depth

couplingFourthEnvelope : Nat → ℚ
couplingFourthEnvelope depth =
  couplingSqEnvelope depth * couplingSqEnvelope depth

couplingFourthStep : ∀ depth →
  couplingFourthEnvelope (suc depth)
  ≡ quarter * couplingFourthEnvelope depth
couplingFourthStep depth = ℚRing.solve-∀

quarticPartialSum : Nat → ℚ
quarticPartialSum zero = 0ℚ
quarticPartialSum (suc depth) =
  quarticPartialSum depth + couplingFourthEnvelope depth

quarticGeometricIdentity : ∀ depth →
  quarticPartialSum depth
    + fourThirds * couplingFourthEnvelope depth
  ≡ fourThirds
quarticGeometricIdentity zero = ℚRing.solve-∀
quarticGeometricIdentity (suc depth) =
  trans
    (cong
      (λ nextPower →
        (quarticPartialSum depth + couplingFourthEnvelope depth)
          + fourThirds * nextPower)
      (couplingFourthStep depth))
    (trans
      (ℚRing.solve-∀)
      (quarticGeometricIdentity depth))

couplingSqNonnegative : ∀ depth → 0ℚ ≤ couplingSqEnvelope depth
couplingSqNonnegative zero =
  let
    instance
      oneNonnegative : NonNegative 1ℚ
      oneNonnegative = ℚP.normalize-nonNeg 1 1
  in ℚP.nonNegative⁻¹ 1ℚ
couplingSqNonnegative (suc depth) =
  let
    halfNonnegativeProof : 0ℚ ≤ half
    halfNonnegativeProof =
      let
        instance
          halfNonnegative : NonNegative half
          halfNonnegative = ℚP.normalize-nonNeg 1 2
      in ℚP.nonNegative⁻¹ half

    instance
      halfNonnegative : NonNegative half
      halfNonnegative = nonNegative halfNonnegativeProof

      previousNonnegative : NonNegative (couplingSqEnvelope depth)
      previousNonnegative = nonNegative (couplingSqNonnegative depth)
  in ℚP.nonNegative⁻¹ (half * couplingSqEnvelope depth)

couplingFourthNonnegative : ∀ depth → 0ℚ ≤ couplingFourthEnvelope depth
couplingFourthNonnegative depth =
  let
    instance
      squareBaseNonnegative : NonNegative (couplingSqEnvelope depth)
      squareBaseNonnegative = nonNegative (couplingSqNonnegative depth)
  in ℚP.nonNegative⁻¹
    (couplingSqEnvelope depth * couplingSqEnvelope depth)

quarticTailNonnegative : ∀ depth →
  0ℚ ≤ fourThirds * couplingFourthEnvelope depth
quarticTailNonnegative depth =
  let
    fourThirdsNonnegativeProof : 0ℚ ≤ fourThirds
    fourThirdsNonnegativeProof =
      let
        instance
          fourThirdsNonnegative : NonNegative fourThirds
          fourThirdsNonnegative = ℚP.normalize-nonNeg 4 3
      in ℚP.nonNegative⁻¹ fourThirds

    instance
      coefficientNonnegative : NonNegative fourThirds
      coefficientNonnegative = nonNegative fourThirdsNonnegativeProof

      powerNonnegative : NonNegative (couplingFourthEnvelope depth)
      powerNonnegative = nonNegative (couplingFourthNonnegative depth)
  in ℚP.nonNegative⁻¹ (fourThirds * couplingFourthEnvelope depth)

quarticPartialSumBelowFourThirds : ∀ depth →
  quarticPartialSum depth ≤ fourThirds
quarticPartialSumBelowFourThirds depth =
  subst
    (λ upper → quarticPartialSum depth ≤ upper)
    (quarticGeometricIdentity depth)
    (baseBelowBasePlusRemainder
      (quarticPartialSum depth)
      (fourThirds * couplingFourthEnvelope depth)
      (quarticTailNonnegative depth))

record QuarticRemainderBound : Set₁ where
  field
    absoluteRemainder : Nat → ℚ
    coefficient : ℚ
    partialAbsoluteRemainder : Nat → ℚ

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      left ≤ leftUpper → right ≤ rightUpper →
      left + right ≤ leftUpper + rightUpper

    partialZero : partialAbsoluteRemainder zero ≡ 0ℚ
    partialStep : ∀ depth →
      partialAbsoluteRemainder (suc depth)
      ≡ partialAbsoluteRemainder depth + absoluteRemainder depth

    remainderControlled : ∀ depth →
      absoluteRemainder depth
      ≤ coefficient * couplingFourthEnvelope depth

open QuarticRemainderBound public

quarticRemainderPartialBound :
  (dataSet : QuarticRemainderBound) → ∀ depth →
  partialAbsoluteRemainder dataSet depth
  ≤ coefficient dataSet * quarticPartialSum depth
quarticRemainderPartialBound dataSet zero =
  subst
    (λ left → left ≤ coefficient dataSet * quarticPartialSum zero)
    (sym (partialZero dataSet))
    (reflexive dataSet 0ℚ)
quarticRemainderPartialBound dataSet (suc depth) =
  subst
    (λ left →
      left ≤ coefficient dataSet * quarticPartialSum (suc depth))
    (sym (partialStep dataSet depth))
    (subst
      (λ upper →
        partialAbsoluteRemainder dataSet depth
          + absoluteRemainder dataSet depth
        ≤ upper)
      (ℚRing.solve-∀)
      (addMonotone dataSet
        (quarticRemainderPartialBound dataSet depth)
        (remainderControlled dataSet depth)))

scalarSchurNormalizationLevel : ProofLevel
scalarSchurNormalizationLevel = machineChecked

gaugeReindexedIntegralWardLevel : ProofLevel
gaugeReindexedIntegralWardLevel = machineChecked

localizationWardCommutationLevel : ProofLevel
localizationWardCommutationLevel = machineChecked

quarticBetaRemainderSummabilityLevel : ProofLevel
quarticBetaRemainderSummabilityLevel = machineChecked

-- The physical producer must identify the actual plaquette coefficient, prove
-- the universal beta normalization and bound its remainder by this quartic (or
-- a sharper harmonic-square) majorant in the shared polymer norm.
physicalWardBetaIdentificationLevel : ProofLevel
physicalWardBetaIdentificationLevel = conditional
