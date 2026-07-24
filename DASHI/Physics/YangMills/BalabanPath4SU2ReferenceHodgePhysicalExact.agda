module DASHI.Physics.YangMills.BalabanPath4SU2ReferenceHodgePhysicalExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact using
  (oneSixteenth)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessian
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact

------------------------------------------------------------------------
-- One coherent owner for the literal side-four reference Hessian.
--
-- The carrier, norm, block constraint, gauge penalty and Q*Q penalty have now
-- been fixed concretely.  The one deliberately exposed producer is the Wilson
-- kinetic identity at the selected reference background.  Supplying that
-- identity cannot alter any of the other operators or norms because they are
-- all projections from the same quadraticData value.
------------------------------------------------------------------------

record Path4SU2ReferenceHodgeData (Gauge Coarse : Set) : Set₁ where
  field
    quadraticData :
      GaugeFixedHessianQuadraticData PhysicalSU2Tangent4 Gauge Coarse ℚ

    nonnegativeIsRationalNonnegative : ∀ value →
      Nonnegative quadraticData value → 0ℚ ≤ value

    referenceCovariantEnergyMatchesDifferenceEnergy : ∀ tangent →
      wilsonHessianQuadraticForm quadraticData tangent
      ≡ physicalReferenceDifferenceEnergy tangent

open Path4SU2ReferenceHodgeData public

referencePenaltyEnergy :
  ∀ {Gauge Coarse} →
  Path4SU2ReferenceHodgeData Gauge Coarse →
  PhysicalSU2Tangent4 → ℚ
referencePenaltyEnergy dataSet tangent =
  gaugeFixingNormSq (quadraticData dataSet) tangent
  + blockAverageNormSq (quadraticData dataSet) tangent

referencePenaltyEnergyNonnegative :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2ReferenceHodgeData Gauge Coarse)
    tangent →
  0ℚ ≤ referencePenaltyEnergy dataSet tangent
referencePenaltyEnergyNonnegative dataSet tangent =
  subst
    (λ left → left ≤ referencePenaltyEnergy dataSet tangent)
    (ℚP.+-identityˡ 0ℚ)
    (ℚP.+-mono-≤
      (nonnegativeIsRationalNonnegative dataSet
        (gaugeFixingNormSq (quadraticData dataSet) tangent)
        (gaugeNormNonnegative (quadraticData dataSet)
          (divergence (hessianData (quadraticData dataSet)) tangent)))
      (nonnegativeIsRationalNonnegative dataSet
        (blockAverageNormSq (quadraticData dataSet) tangent)
        (coarseNormNonnegative (quadraticData dataSet)
          (average (hessianData (quadraticData dataSet)) tangent))))

referenceWilsonBelowGaugeFixedHessian :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2ReferenceHodgeData Gauge Coarse)
    tangent →
  wilsonHessianQuadraticForm (quadraticData dataSet) tangent
  ≤ gaugeFixedHessianQuadraticForm (quadraticData dataSet) tangent
referenceWilsonBelowGaugeFixedHessian dataSet tangent =
  subst
    (λ right →
      wilsonHessianQuadraticForm (quadraticData dataSet) tangent ≤ right)
    (sym (gaugeFixedHessianQuadraticFormExact
      (quadraticData dataSet) tangent))
    (baseBelowBasePlusRemainder
      (wilsonHessianQuadraticForm (quadraticData dataSet) tangent)
      (referencePenaltyEnergy dataSet tangent)
      (referencePenaltyEnergyNonnegative dataSet tangent))

referenceDifferenceBelowPhysicalHessian :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2ReferenceHodgeData Gauge Coarse)
    tangent →
  physicalReferenceDifferenceEnergy tangent
  ≤ gaugeFixedHessianQuadraticForm (quadraticData dataSet) tangent
referenceDifferenceBelowPhysicalHessian dataSet tangent =
  subst
    (λ left →
      left ≤ gaugeFixedHessianQuadraticForm (quadraticData dataSet) tangent)
    (referenceCovariantEnergyMatchesDifferenceEnergy dataSet tangent)
    (referenceWilsonBelowGaugeFixedHessian dataSet tangent)

uniformReferenceHodgeCoercivity :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2ReferenceHodgeData Gauge Coarse)
    tangent →
  PhysicalBlockAverageZero tangent →
  oneSixteenth * physicalUnweightedNormSq tangent
  ≤ gaugeFixedHessianQuadraticForm (quadraticData dataSet) tangent
uniformReferenceHodgeCoercivity dataSet tangent blockZero =
  ℚP.≤-trans
    (physicalBlockConstrainedDifferencePoincare tangent blockZero)
    (referenceDifferenceBelowPhysicalHessian dataSet tangent)

path4SU2ReferencePenaltyExactLevel : ProofLevel
path4SU2ReferencePenaltyExactLevel = machineChecked

path4SU2ReferenceHodgeAssemblyLevel : ProofLevel
path4SU2ReferenceHodgeAssemblyLevel = machineChecked

referenceWilsonDifferenceIdentificationLevel : ProofLevel
referenceWilsonDifferenceIdentificationLevel = conditional
