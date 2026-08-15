module DASHI.Physics.YangMills.BalabanCMP109FederbushCancellationNormalizedInverseExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Consume the exact Lie-theoretic cancellation
--
--       J_+(Y) Ad_{exp Y} = J_-(Y)
--
-- at the finite rational matrix boundary.  A caller identifies each physical
-- component J_j T_j with the opposite-trivialization inverse-dexp matrix and
-- supplies its source-radius defect bound.  The normalized residual is then
-- controlled directly, without separately paying for T_j-I.
--
-- At |Y|<=1/12 the source inverse-dexp envelope
--
--       t/2 + t^2/6 = 37/864
--
-- is already far below 1/4.  Thus the component cancellation gives a much
-- larger conditioning margin than the earlier triangle budget.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedResidualReopeningExact as Normalized
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanCMP109FederbushSourceScaleQuarterExact as SourceScale

record FederbushCancellationData (Index : Set) : Set₁ where
  field
    indices : List Index
    weight : ℚ

    physicalComponent oppositeInverseDexp : Index → Jacobian.Lie3Matrix

    weightNonnegative : 0ℚ ≤ weight
    normalizedWeight :
      weight * Fibre.natAsRational (length indices) ≡ 1ℚ

    componentCancellation : ∀ index row column →
      physicalComponent index row column
      ≡ oppositeInverseDexp index row column

    oppositeInverseDexpSourceDefect : ∀ index column →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.logJacobianResidual (oppositeInverseDexp index)) column
      ≤ SourceScale.sourceLogDefectBound

open FederbushCancellationData public

physicalComponentResidual :
  ∀ {Index} → FederbushCancellationData Index →
  Index → Jacobian.Lie3Matrix
physicalComponentResidual dataSet index =
  Component.logJacobianResidual (physicalComponent dataSet index)

componentResidualEqualsOppositeInverseDefect :
  ∀ {Index} (dataSet : FederbushCancellationData Index)
    index row column →
  physicalComponentResidual dataSet index row column
  ≡ Component.logJacobianResidual
      (oppositeInverseDexp dataSet index) row column
componentResidualEqualsOppositeInverseDefect dataSet index row column =
  cong
    (λ value → value - Jacobian.identity3 row column)
    (componentCancellation dataSet index row column)
  where
  open import Data.Rational.Base using (_-_)

sourceLogDefectFitsQuarter :
  SourceScale.sourceLogDefectBound ≤ Quarter.oneQuarter
sourceLogDefectFitsQuarter =
  ℚP.≤-trans
    (oppositeInverseDexpSourceDefectDummy)
    ℚP.≤-refl
  where
  -- Keep the proof as a literal rational comparison; the local dummy theorem
  -- simply avoids importing another arithmetic helper.
  oppositeInverseDexpSourceDefectDummy :
    SourceScale.sourceLogDefectBound ≤ Quarter.oneQuarter
  oppositeInverseDexpSourceDefectDummy =
    DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact.nonnegativeDifferenceImpliesBelow
      (ℚP.nonNegative⁻¹
        (Quarter.oneQuarter - SourceScale.sourceLogDefectBound))
    where
    open import Data.Rational.Base using (_-_)
    import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact

localCancellationResidualQuarter :
  ∀ {Index} (dataSet : FederbushCancellationData Index) index column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (physicalComponentResidual dataSet index) column
  ≤ Quarter.oneQuarter
localCancellationResidualQuarter dataSet index column =
  let
    identify :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (physicalComponentResidual dataSet index) column
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.logJacobianResidual
          (oppositeInverseDexp dataSet index)) column
    identify = Sums.sumRationalCong Physical.lieCoordinates3 _ _
      (λ row → cong ∣_∣
        (componentResidualEqualsOppositeInverseDefect
          dataSet index row column))
  in
  ℚP.≤-trans
    (subst
      (λ lower → lower ≤ SourceScale.sourceLogDefectBound)
      identify
      (oppositeInverseDexpSourceDefect dataSet index column))
    sourceLogDefectFitsQuarter

asQuarterResidualData :
  ∀ {Index} → FederbushCancellationData Index →
  Normalized.FederbushQuarterResidualData Index
asQuarterResidualData dataSet = record
  { Normalized.FederbushQuarterResidualData.indices = indices dataSet
  ; Normalized.FederbushQuarterResidualData.weight = weight dataSet
  ; Normalized.FederbushQuarterResidualData.residual =
      physicalComponentResidual dataSet
  ; Normalized.FederbushQuarterResidualData.weightNonnegative =
      weightNonnegative dataSet
  ; Normalized.FederbushQuarterResidualData.normalizedWeight =
      normalizedWeight dataSet
  ; Normalized.FederbushQuarterResidualData.localColumnQuarter =
      localCancellationResidualQuarter dataSet
  }

cancellationFederbushEquation :
  ∀ {Index} → FederbushCancellationData Index →
  Jacobian.Lie3Vector → Jacobian.Lie3Vector → Set
cancellationFederbushEquation dataSet =
  Normalized.normalizedFederbushEquation (asQuarterResidualData dataSet)

cancellationInverseFourThirds :
  ∀ {Index} (dataSet : FederbushCancellationData Index)
    solution source →
  cancellationFederbushEquation dataSet solution source →
  L1.vectorL1 Physical.lieCoordinates3 solution
  ≤ Quarter.fourThirds * L1.vectorL1 Physical.lieCoordinates3 source
cancellationInverseFourThirds dataSet =
  Normalized.normalizedFederbushSolutionL1FourThirds
    (asQuarterResidualData dataSet)

cancellationKernelTrivial :
  ∀ {Index} (dataSet : FederbushCancellationData Index) solution →
  cancellationFederbushEquation dataSet solution Reopen.zeroVector →
  ∀ coordinate → solution coordinate ≡ 0ℚ
cancellationKernelTrivial dataSet =
  Normalized.normalizedFederbushHomogeneousKernelTrivial
    (asQuarterResidualData dataSet)

cmp109FederbushCancellationResidualQuarterLevel : ProofLevel
cmp109FederbushCancellationResidualQuarterLevel = machineChecked

cmp109FederbushCancellationFourThirdsInverseLevel : ProofLevel
cmp109FederbushCancellationFourThirdsInverseLevel = machineChecked

-- Remaining G1 identification: connect the Real reduced-operator cancellation
-- theorem to these literal rational 3x3 matrices and instantiate the opposite-
-- trivialization inverse-dexp source-radius defect bound.
cmp109FederbushCancellationMatrixDictionaryLevel : ProofLevel
cmp109FederbushCancellationMatrixDictionaryLevel = conditional
