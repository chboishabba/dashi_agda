module DASHI.Physics.YangMills.BalabanPath4SU2ReferenceHodgePhysicalExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate using
  (configuredPathCoercivityConstant;
   configuredPathCoercivityConstantPositive)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessian
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact

------------------------------------------------------------------------
-- One coherent owner for the literal configured-side reference Hessian.
--
-- The Wilson second variation is the curl part of the reference Hodge form;
-- the gauge-fixing quadratic form is the longitudinal part.  Consequently the
-- physical finite-difference energy is identified with their sum, not with the
-- Wilson term alone.  Q*Q remains the independent nonnegative block penalty.
------------------------------------------------------------------------

cReference : ℚ
cReference = configuredPathCoercivityConstant

cReferencePositive : 0ℚ < cReference
cReferencePositive = configuredPathCoercivityConstantPositive

record Path4SU2ReferenceHodgeData (Gauge Coarse : Set) : Set₁ where
  field
    quadraticData :
      GaugeFixedHessianQuadraticData PhysicalSU2Tangent4 Gauge Coarse ℚ

    addScalarMatchesRationalAddition : ∀ left right →
      addScalar quadraticData left right ≡ left + right

    nonnegativeIsRationalNonnegative : ∀ value →
      Nonnegative quadraticData value → 0ℚ ≤ value

    referenceWilsonGaugeEnergyMatchesDifferenceEnergy : ∀ tangent →
      wilsonHessianQuadraticForm quadraticData tangent
      + gaugeFixingNormSq quadraticData tangent
      ≡ physicalReferenceDifferenceEnergy tangent

open Path4SU2ReferenceHodgeData public

referenceBlockPenaltyNonnegative :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2ReferenceHodgeData Gauge Coarse)
    tangent →
  0ℚ ≤ blockAverageNormSq (quadraticData dataSet) tangent
referenceBlockPenaltyNonnegative dataSet tangent =
  nonnegativeIsRationalNonnegative dataSet
    (blockAverageNormSq (quadraticData dataSet) tangent)
    (coarseNormNonnegative (quadraticData dataSet)
      (average (hessianData (quadraticData dataSet)) tangent))

nestedScalarAdditionExact :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2ReferenceHodgeData Gauge Coarse)
    left middle right →
  addScalar (quadraticData dataSet) left
    (addScalar (quadraticData dataSet) middle right)
  ≡ left + (middle + right)
nestedScalarAdditionExact dataSet left middle right =
  trans
    (addScalarMatchesRationalAddition dataSet left
      (addScalar (quadraticData dataSet) middle right))
    (cong (λ value → left + value)
      (addScalarMatchesRationalAddition dataSet middle right))

gaugeFixedHessianPhysicalDecompositionExact :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2ReferenceHodgeData Gauge Coarse)
    tangent →
  gaugeFixedHessianQuadraticForm (quadraticData dataSet) tangent
  ≡ physicalReferenceDifferenceEnergy tangent
    + blockAverageNormSq (quadraticData dataSet) tangent
gaugeFixedHessianPhysicalDecompositionExact dataSet tangent =
  trans
    (gaugeFixedHessianQuadraticFormExact
      (quadraticData dataSet) tangent)
    (trans
      (nestedScalarAdditionExact dataSet
        (wilsonHessianQuadraticForm (quadraticData dataSet) tangent)
        (gaugeFixingNormSq (quadraticData dataSet) tangent)
        (blockAverageNormSq (quadraticData dataSet) tangent))
      (trans
        (ℚRing.solve-∀
          (wilsonHessianQuadraticForm (quadraticData dataSet) tangent)
          (gaugeFixingNormSq (quadraticData dataSet) tangent)
          (blockAverageNormSq (quadraticData dataSet) tangent))
        (cong₂ _+_
          (referenceWilsonGaugeEnergyMatchesDifferenceEnergy dataSet tangent)
          refl)))

referenceDifferenceBelowPhysicalHessian :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2ReferenceHodgeData Gauge Coarse)
    tangent →
  physicalReferenceDifferenceEnergy tangent
  ≤ gaugeFixedHessianQuadraticForm (quadraticData dataSet) tangent
referenceDifferenceBelowPhysicalHessian dataSet tangent =
  subst
    (λ right → physicalReferenceDifferenceEnergy tangent ≤ right)
    (sym (gaugeFixedHessianPhysicalDecompositionExact dataSet tangent))
    (baseBelowBasePlusRemainder
      (physicalReferenceDifferenceEnergy tangent)
      (blockAverageNormSq (quadraticData dataSet) tangent)
      (referenceBlockPenaltyNonnegative dataSet tangent))

uniformReferenceHodgeCoercivity :
  ∀ {Gauge Coarse}
    (dataSet : Path4SU2ReferenceHodgeData Gauge Coarse)
    tangent →
  PhysicalBlockAverageZero tangent →
  cReference * physicalUnweightedNormSq tangent
  ≤ gaugeFixedHessianQuadraticForm (quadraticData dataSet) tangent
uniformReferenceHodgeCoercivity dataSet tangent blockZero =
  ℚP.≤-trans
    (physicalBlockConstrainedDifferencePoincare tangent blockZero)
    (referenceDifferenceBelowPhysicalHessian dataSet tangent)

path4SU2ReferencePenaltyExactLevel : ProofLevel
path4SU2ReferencePenaltyExactLevel = machineChecked

path4SU2ReferenceHodgeAssemblyLevel : ProofLevel
path4SU2ReferenceHodgeAssemblyLevel = machineChecked

cReferencePositiveLevel : ProofLevel
cReferencePositiveLevel = machineChecked

referenceWilsonGaugeDifferenceIdentificationLevel : ProofLevel
referenceWilsonGaugeDifferenceIdentificationLevel = conditional
