module DASHI.Physics.YangMills.BalabanDegreeOneStateNormG2HeadroomNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- The exact degree-one defect calculation is also a falsifier for the tempting
-- strategy "bound raw, source norm and defect norm separately, then polarize".
-- Since
--
--      defectRatio = 1/3,
--
-- the polarization Green cost alone contributes
--
--      (1/2)(1/3) = 1/6.
--
-- But the entire singleton budget is only
--
--      55 / 18874368.
--
-- Under the ordinary nonnegative-majorant convention for raw and source norm
-- ratios, the resulting degree-one state-norm residual majorant is therefore
-- STRICTLY larger than the complete singleton budget before either estimate is
-- even spent. Numerically the gap factor is 3145728/55 > 57195.
--
-- This proves that the high-alpha G2 route must estimate the correlated
-- degree-one object raw_1 - G_11 before polarization/absolute-value loss (or
-- exploit an equally strong signed cancellation). It prevents future work
-- from wasting effort optimizing two estimates that cannot close the target.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
open import Relation.Nullary.Negation using (¬_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanChargeRelativeDegreeOneG2ClosureExact as G2
import DASHI.Physics.YangMills.BalabanChargeRelativeDegreeOneG2ExactDefectCompiler as ExactDefect

oneSixth : ℚ
oneSixth = + 1 / 6

target : ℚ
target = Selector.remainingSingletonCoefficient

headroomExcess : ℚ
headroomExcess = oneSixth - target

headroomExcessPositive : 0ℚ < headroomExcess
headroomExcessPositive =
  subst
    (0ℚ <_)
    (ℚRing.solve [] : headroomExcess ≡ + 3145673 / 18874368)
    (ℚP.positive⁻¹ (+ 3145673 / 18874368))

targetPlusExcessIsOneSixth :
  target + headroomExcess ≡ oneSixth
targetPlusExcessIsOneSixth = ℚRing.solve []

targetStrictlyBelowOneSixth : target < oneSixth
targetStrictlyBelowOneSixth =
  let
    shifted : 0ℚ + target < headroomExcess + target
    shifted = ℚP.+-monoʳ-< target headroomExcessPositive
    leftMeaning : 0ℚ + target ≡ target
    leftMeaning = ℚRing.solve []
    rightMeaning : headroomExcess + target ≡ oneSixth
    rightMeaning = ℚRing.solve []
  in
  subst₂ _<_ leftMeaning rightMeaning shifted

record NonnegativeSeparateMajorants
    {Configuration Multiplier : Set}
    (dataSet : ExactDefect.ExactDefectDegreeOneG2Data
      Configuration Multiplier) : Set where
  field
    rawTotalNonnegative :
      0ℚ ≤ G2.rawRatioTotal (ExactDefect.toDegreeOneG2Data dataSet)
    sourceRatioNonnegative :
      0ℚ ≤ ExactDefect.sourceDegreeOneNormRatio dataSet

open NonnegativeSeparateMajorants public

residualMajorantAtLeastOneSixth :
  ∀ {Configuration Multiplier}
    {dataSet : ExactDefect.ExactDefectDegreeOneG2Data
      Configuration Multiplier} →
  NonnegativeSeparateMajorants dataSet →
  oneSixth ≤ ExactDefect.exactDefectResidualRatio dataSet
residualMajorantAtLeastOneSixth {dataSet = dataSet} nonnegative =
  let
    raw = G2.rawRatioTotal (ExactDefect.toDegreeOneG2Data dataSet)
    source = ExactDefect.sourceDegreeOneNormRatio dataSet
    residual = ExactDefect.exactDefectResidualRatio dataSet

    halfSourceNonnegative : 0ℚ ≤ (+ 1 / 2) * source
    halfSourceNonnegative =
      let
        instance halfNN : NonNegative (+ 1 / 2)
        halfNN = ℚ.nonNegative (ℚP.nonNegative⁻¹ (+ 1 / 2))
        sourceNN : NonNegative source
        sourceNN = ℚ.nonNegative (sourceRatioNonnegative nonnegative)
      in
      ℚP.nonNegative⁻¹ ((+ 1 / 2) * source)

    excessNonnegative : 0ℚ ≤ raw + (+ 1 / 2) * source
    excessNonnegative = ℚP.+-mono-≤
      (rawTotalNonnegative nonnegative)
      halfSourceNonnegative

    residualMinusFloorNonnegative : 0ℚ ≤ residual - oneSixth
    residualMinusFloorNonnegative =
      subst
        (0ℚ ≤_)
        (sym
          (ℚRing.solve-∀ raw source :
            residual - oneSixth ≡ raw + (+ 1 / 2) * source))
        excessNonnegative
  in
  Norm.nonnegativeDifferenceImpliesBelow residualMinusFloorNonnegative

separateMajorantsStrictlyMissHeadroom :
  ∀ {Configuration Multiplier}
    {dataSet : ExactDefect.ExactDefectDegreeOneG2Data
      Configuration Multiplier} →
  NonnegativeSeparateMajorants dataSet →
  target < ExactDefect.exactDefectResidualRatio dataSet
separateMajorantsStrictlyMissHeadroom nonnegative =
  ℚP.<-≤-trans targetStrictlyBelowOneSixth
    (residualMajorantAtLeastOneSixth nonnegative)

separateMajorantsCannotCloseSingleton :
  ∀ {Configuration Multiplier}
    {dataSet : ExactDefect.ExactDefectDegreeOneG2Data
      Configuration Multiplier} →
  NonnegativeSeparateMajorants dataSet →
  ¬ (ExactDefect.exactDefectResidualRatio dataSet ≤ target)
separateMajorantsCannotCloseSingleton nonnegative =
  ℚP.<⇒≱ (separateMajorantsStrictlyMissHeadroom nonnegative)

degreeOneStateNormG2HeadroomNoGoLevel : ProofLevel
degreeOneStateNormG2HeadroomNoGoLevel = machineChecked

-- New live G2 producer after this falsifier:
--   bound the signed correlated D1 residual raw_1 - G_11 directly,
--   then add only whatever raw higher-degree terms genuinely survive.
correlatedDegreeOneBeforePolarizationProducerLevel : ProofLevel
correlatedDegreeOneBeforePolarizationProducerLevel = conditional
