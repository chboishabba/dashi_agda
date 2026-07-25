module DASHI.Physics.YangMills.BalabanPath4SU2LiteralGaugeFixedHessianAdapterExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate using
  (configuredPathCoercivityConstant)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact using
  (literalWilsonHessianPositivePlaneFold)
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact using
  (literalGaugeFixingEnergy; physicalPeriodicReferenceDifferenceEnergy)
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicReferenceHodgeExact using
  ( literalWilsonGaugeEqualsPeriodicDifferenceEnergy
  ; physicalReferenceDifferenceBelowPeriodic
  )

------------------------------------------------------------------------
-- Exact adapter from the repository operator record to the concrete literal
-- Wilson and divergence folds.  No Hodge or normalization theorem is assumed.
------------------------------------------------------------------------

record Path4SU2LiteralGaugeFixedHessianData (Gauge Coarse : Set) : Set₁ where
  field
    quadraticData :
      GaugeFixedHessianQuadraticData PhysicalSU2Tangent4 Gauge Coarse ℚ

    addScalarMatchesRationalAddition : ∀ left right →
      addScalar quadraticData left right ≡ left + right

    nonnegativeIsRationalNonnegative : ∀ value →
      Nonnegative quadraticData value → 0ℚ ≤ value

    wilsonHessianMatchesLiteral : ∀ tangent →
      wilsonHessianQuadraticForm quadraticData tangent
      ≡ literalWilsonHessianPositivePlaneFold tangent

    gaugeFixingMatchesLiteral : ∀ tangent →
      gaugeFixingNormSq quadraticData tangent
      ≡ literalGaugeFixingEnergy tangent

open Path4SU2LiteralGaugeFixedHessianData public

literalAdapterBlockPenaltyNonnegative :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2LiteralGaugeFixedHessianData Gauge Coarse)
    tangent →
  0ℚ ≤ blockAverageNormSq (quadraticData dataSet) tangent
literalAdapterBlockPenaltyNonnegative dataSet tangent =
  nonnegativeIsRationalNonnegative dataSet
    (blockAverageNormSq (quadraticData dataSet) tangent)
    (coarseNormNonnegative (quadraticData dataSet)
      (average (hessianData (quadraticData dataSet)) tangent))

literalAdapterNestedAddition :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2LiteralGaugeFixedHessianData Gauge Coarse)
    left middle right →
  addScalar (quadraticData dataSet) left
    (addScalar (quadraticData dataSet) middle right)
  ≡ left + (middle + right)
literalAdapterNestedAddition dataSet left middle right =
  trans
    (addScalarMatchesRationalAddition dataSet left
      (addScalar (quadraticData dataSet) middle right))
    (cong (λ value → left + value)
      (addScalarMatchesRationalAddition dataSet middle right))

literalGaugeFixedHessianPeriodicDecompositionExact :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2LiteralGaugeFixedHessianData Gauge Coarse)
    tangent →
  gaugeFixedHessianQuadraticForm (quadraticData dataSet) tangent
  ≡ physicalPeriodicReferenceDifferenceEnergy tangent
    + blockAverageNormSq (quadraticData dataSet) tangent
literalGaugeFixedHessianPeriodicDecompositionExact dataSet tangent =
  trans
    (gaugeFixedHessianQuadraticFormExact
      (quadraticData dataSet) tangent)
    (trans
      (literalAdapterNestedAddition dataSet
        (wilsonHessianQuadraticForm (quadraticData dataSet) tangent)
        (gaugeFixingNormSq (quadraticData dataSet) tangent)
        (blockAverageNormSq (quadraticData dataSet) tangent))
      (trans
        (ℚRing.solve-∀
          (wilsonHessianQuadraticForm (quadraticData dataSet) tangent)
          (gaugeFixingNormSq (quadraticData dataSet) tangent)
          (blockAverageNormSq (quadraticData dataSet) tangent))
        (cong₂ _+_
          (trans
            (cong₂ _+_
              (wilsonHessianMatchesLiteral dataSet tangent)
              (gaugeFixingMatchesLiteral dataSet tangent))
            (literalWilsonGaugeEqualsPeriodicDifferenceEnergy tangent))
          refl)))

physicalDifferenceBelowLiteralGaugeFixedHessian :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2LiteralGaugeFixedHessianData Gauge Coarse)
    tangent →
  physicalReferenceDifferenceEnergy tangent
  ≤ gaugeFixedHessianQuadraticForm (quadraticData dataSet) tangent
physicalDifferenceBelowLiteralGaugeFixedHessian dataSet tangent =
  subst
    (λ right → physicalReferenceDifferenceEnergy tangent ≤ right)
    (sym (literalGaugeFixedHessianPeriodicDecompositionExact dataSet tangent))
    (ℚP.≤-trans
      (physicalReferenceDifferenceBelowPeriodic tangent)
      (baseBelowBasePlusRemainder
        (physicalPeriodicReferenceDifferenceEnergy tangent)
        (blockAverageNormSq (quadraticData dataSet) tangent)
        (literalAdapterBlockPenaltyNonnegative dataSet tangent)))

uniformReferenceHodgeCoercivityFromLiteralProducer :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2LiteralGaugeFixedHessianData Gauge Coarse)
    tangent →
  PhysicalBlockAverageZero tangent →
  configuredPathCoercivityConstant * physicalUnweightedNormSq tangent
  ≤ gaugeFixedHessianQuadraticForm (quadraticData dataSet) tangent
uniformReferenceHodgeCoercivityFromLiteralProducer dataSet tangent blockZero =
  ℚP.≤-trans
    (physicalBlockConstrainedDifferencePoincare tangent blockZero)
    (physicalDifferenceBelowLiteralGaugeFixedHessian dataSet tangent)

literalGaugeFixedHessianPeriodicAdapterLevel : ProofLevel
literalGaugeFixedHessianPeriodicAdapterLevel = machineChecked

uniformReferenceHodgeCoercivityFromLiteralProducerLevel : ProofLevel
uniformReferenceHodgeCoercivityFromLiteralProducerLevel = machineChecked
