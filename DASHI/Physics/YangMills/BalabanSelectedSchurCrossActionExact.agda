module DASHI.Physics.YangMills.BalabanSelectedSchurCrossActionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Balaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Identify the defect cross matrix C_A used by the quantitative Schur bound
-- with the literal off-diagonal blocks of the selected combined constraint
-- Gram.  The key exact observation is that A^* alpha is constant in the site
-- coordinate for each Lie-coordinate/direction pair, hence the flat periodic
-- divergence annihilates it:
--
--       L_gauge,0 A^* alpha = 0.
--
-- Therefore
--
--       L_gauge,A A^* alpha = D_A A^* alpha = C_A alpha.
--
-- On the reverse block, finite adjointness gives
--
--       C_A^T gamma = A D_A^* gamma,
--
-- and the existing defect-only theorem identifies this with
-- A L_gauge,A^* gamma for a reduced gauge multiplier.  Thus
-- (1/256) C_A C_A^T is the actual Schur correction of the 256 I average block,
-- not an auxiliary comparison matrix.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as GaugeFirst
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFiniteRationalReopeningExact as Carrier
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as Defect
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeOperatorDecompositionExact as GaugeOperator
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageSectionExact as AverageSection
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageRowCarrierExact as AverageRows
import DASHI.Physics.YangMills.BalabanSelectedSchurCrossAbsoluteMassExact as Cross
import DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact as Split
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintGramBlockSchurExact as BlockSchur
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintSchurCrossDefectOnlyExact as DefectOnly

AverageRow : Set
AverageRow = Average.SelectedBlockAverageRow4

AverageMultiplier : Set
AverageMultiplier = AverageRow → ℚ

GaugeRow : Set
GaugeRow = Cross.GaugeRow

GaugeMultiplier : Set
GaugeMultiplier = GaugeRow → ℚ

averageBasisStateIsAverageMatrixEntry : ∀ target column →
  Cross.averageBasisState target column
  ≡ Average.selectedBackgroundBlockAverageConstraintMatrix target column
averageBasisStateIsAverageMatrixEntry target column =
  trans
    (sym
      (AverageRows.selectedBlockAverageTransposeApplyExact
        (Cross.averageBasisMultiplier target) column))
    (Basis.selectorExact
      AverageRows.selectedBlockAverageRowFiniteSelector
      (λ row → Average.selectedBackgroundBlockAverageConstraintMatrix row column)
      target)

selectedSchurCrossIsDefectCompose : ∀ background gaugeRow averageRow →
  Cross.selectedSchurCrossMatrix background gaugeRow averageRow
  ≡ Rect.composeRectangular KKT.physicalStateCarrier
      (Defect.gaugeDefectMatrix background)
      (Rect.transposeRectangular
        Average.selectedBackgroundBlockAverageConstraintMatrix)
      gaugeRow averageRow
selectedSchurCrossIsDefectCompose background gaugeRow averageRow =
  Sums.sumRationalCong Coordinates.physicalSU2Coordinates4 _ _
    (λ column →
      cong
        (Defect.gaugeDefectMatrix background gaugeRow column *_)
        (averageBasisStateIsAverageMatrixEntry averageRow column))

selectedSchurCrossForwardApply :
  Physical.RationalSU2Background4 → AverageMultiplier → GaugeMultiplier
selectedSchurCrossForwardApply background =
  Rect.applyRectangular AverageRows.selectedBlockAverageRowCarrier
    (Cross.selectedSchurCrossMatrix background)

selectedSchurCrossForwardIsDefectOnAverageAdjoint :
  ∀ background average gaugeRow →
  selectedSchurCrossForwardApply background average gaugeRow
  ≡ GaugeOperator.gaugeDefectForwardApply background
      (AverageSection.selectedBlockAverageAdjointLift average) gaugeRow
selectedSchurCrossForwardIsDefectOnAverageAdjoint background average gaugeRow =
  let
    identify :
      selectedSchurCrossForwardApply background average gaugeRow
      ≡ Rect.applyRectangular AverageRows.selectedBlockAverageRowCarrier
          (Rect.composeRectangular KKT.physicalStateCarrier
            (Defect.gaugeDefectMatrix background)
            (Rect.transposeRectangular
              Average.selectedBackgroundBlockAverageConstraintMatrix))
          average gaugeRow
    identify = Sums.sumRationalCong
      (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector) _ _
      (λ averageRow →
        cong (_* average averageRow)
          (selectedSchurCrossIsDefectCompose
            background gaugeRow averageRow))

    compose = Rect.applyComposeRectangularExact
      KKT.physicalStateCarrier
      AverageRows.selectedBlockAverageRowCarrier
      (Defect.gaugeDefectMatrix background)
      (Rect.transposeRectangular
        Average.selectedBackgroundBlockAverageConstraintMatrix)
      average gaugeRow

    innerCong = Rect.applyRectangularVectorCong
      KKT.physicalStateCarrier
      (Defect.gaugeDefectMatrix background)
      (AverageRows.selectedBlockAverageTransposeApplyExact average)
      gaugeRow
  in
  trans identify (trans compose innerCong)

averageAdjointFlatAxesZero :
  ∀ average coordinate site →
  GaugeFirst.flatGaugeFirstFromAxes
    (Coordinates.decodePhysicalSU2
      (AverageSection.selectedBlockAverageAdjointLift average))
    (pair coordinate site)
  ≡ 0ℚ
averageAdjointFlatAxesZero average coordinate site =
  ℚRing.solve-∀
    (average (pair coordinate Periodic.axis0))
    (average (pair coordinate Periodic.axis1))
    (average (pair coordinate Periodic.axis2))
    (average (pair coordinate Periodic.axis3))

averageAdjointFlatGaugeFirstZero :
  ∀ average coordinate site →
  FlatGauge.flatGaugeFirst
    (Coordinates.decodePhysicalSU2
      (AverageSection.selectedBlockAverageAdjointLift average))
    (pair coordinate site)
  ≡ 0ℚ
averageAdjointFlatGaugeFirstZero average coordinate site =
  trans
    (sym
      (GaugeFirst.flatGaugeFirstFromAxesIsPeriodicDivergence
        (Coordinates.decodePhysicalSU2
          (AverageSection.selectedBlockAverageAdjointLift average))
        coordinate site))
    (averageAdjointFlatAxesZero average coordinate site)

flatGaugeMatrixOnAverageAdjointZero :
  ∀ average row →
  Rect.applyRectangular KKT.physicalStateCarrier
    (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
      Physical.identityBackground)
    (AverageSection.selectedBlockAverageAdjointLift average) row
  ≡ 0ℚ
flatGaugeMatrixOnAverageAdjointZero average (pair coordinate site) =
  trans
    (GaugeMatrix.selectedBackgroundGaugeConstraintMatrixApplyExact
      Physical.identityBackground
      (AverageSection.selectedBlockAverageAdjointLift average)
      (pair coordinate site))
    (trans
      (GaugeFirst.identityBackgroundGaugeFirstIsPeriodicDivergence
        (Coordinates.decodePhysicalSU2
          (AverageSection.selectedBlockAverageAdjointLift average))
        coordinate site)
      (averageAdjointFlatGaugeFirstZero average coordinate site))

backgroundGaugeOnAverageAdjointIsDefect :
  ∀ background average row →
  GaugeOperator.backgroundGaugeConstraintApply background
    (AverageSection.selectedBlockAverageAdjointLift average) row
  ≡ GaugeOperator.gaugeDefectForwardApply background
      (AverageSection.selectedBlockAverageAdjointLift average) row
backgroundGaugeOnAverageAdjointIsDefect background average row =
  let
    state = AverageSection.selectedBlockAverageAdjointLift average
  in
  trans
    (GaugeOperator.backgroundGaugeConstraintSplits background state row)
    (trans
      (cong (_+ GaugeOperator.gaugeDefectForwardApply background state row)
        (flatGaugeMatrixOnAverageAdjointZero average row))
      (ℚRing.solve-∀
        (GaugeOperator.gaugeDefectForwardApply background state row)))

selectedSchurCrossTransposeApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → AverageMultiplier
selectedSchurCrossTransposeApply background gauge averageRow =
  Sums.sumRational Cross.gaugeRows
    (λ gaugeRow →
      Cross.selectedSchurCrossMatrix background gaugeRow averageRow
        * gauge gaugeRow)

selectedSchurCrossTransposeIsAverageDefectCross :
  ∀ background gauge averageRow →
  selectedSchurCrossTransposeApply background gauge averageRow
  ≡ Average.selectedBackgroundBlockAverageConstraintApply
      (Defect.gaugeAdjointDefectApply background gauge) averageRow
selectedSchurCrossTransposeIsAverageDefectCross background gauge averageRow =
  let
    basis = Cross.averageBasisState averageRow
    basisMultiplier = Cross.averageBasisMultiplier averageRow
    defectState = Defect.gaugeAdjointDefectApply background gauge

    leftAsDot :
      selectedSchurCrossTransposeApply background gauge averageRow
      ≡ Rect.finiteDot Carrier.gaugeFiniteCoordinates
          (GaugeOperator.gaugeDefectForwardApply background basis) gauge
    leftAsDot = Sums.sumRationalCong Cross.gaugeRows _ _
      (λ gaugeRow → refl)

    adjoint = Rect.rectangularAdjointExact
      Carrier.gaugeFiniteCoordinates
      KKT.physicalStateCarrier
      (Defect.gaugeDefectMatrix background)
      basis gauge

    swapStateDot = Rect.finiteDotSymmetric
      KKT.physicalStateCarrier basis defectState

    basisExact : ∀ coordinate →
      basis coordinate
      ≡ AverageSection.selectedBlockAverageAdjointLift basisMultiplier coordinate
    basisExact coordinate = refl

    stateDotToPhysical :
      Rect.finiteDot KKT.physicalStateCarrier defectState basis
      ≡ Coordinates.physicalCoordinateDot defectState
          (AverageSection.selectedBlockAverageAdjointLift basisMultiplier)
    stateDotToPhysical = Sums.sumRationalCong Coordinates.physicalSU2Coordinates4 _ _
      (λ coordinate → cong (defectState coordinate *_) (basisExact coordinate))

    averageAdjoint = AverageSection.selectedBlockAverageAdjointExact
      defectState basisMultiplier

    rowDotSelect :
      AverageSection.selectedBlockAverageRowDot
        (Average.selectedBackgroundBlockAverageConstraintApply defectState)
        basisMultiplier
      ≡ Average.selectedBackgroundBlockAverageConstraintApply defectState averageRow
    rowDotSelect =
      trans
        (Sums.sumRationalCong Average.selectedBlockAverageRows4 _ _
          (λ row → ℚP.*-comm
            (Average.selectedBackgroundBlockAverageConstraintApply defectState row)
            (basisMultiplier row)))
        (AverageRows.selectedBlockAverageRowDeltaActsAsIdentity
          (Average.selectedBackgroundBlockAverageConstraintApply defectState)
          averageRow)
  in
  trans leftAsDot
    (trans adjoint
      (trans swapStateDot
        (trans stateDotToPhysical
          (trans (sym averageAdjoint) rowDotSelect))))

selectedSchurCrossForwardIsPhysicalGaugeAverageCross :
  ∀ background selected row →
  selectedSchurCrossForwardApply background
    (Split.averageMultiplier selected) row
  ≡ BlockSchur.gaugeAverageCross background selected row
selectedSchurCrossForwardIsPhysicalGaugeAverageCross background selected row =
  trans
    (selectedSchurCrossForwardIsDefectOnAverageAdjoint
      background (Split.averageMultiplier selected) row)
    (sym
      (backgroundGaugeOnAverageAdjointIsDefect
        background (Split.averageMultiplier selected) row))

selectedSchurCrossTransposeIsPhysicalAverageGaugeCross :
  ∀ background selected averageRow →
  selectedSchurCrossTransposeApply background
    (Split.gaugeMultiplier selected) averageRow
  ≡ BlockSchur.averageGaugeCross background selected averageRow
selectedSchurCrossTransposeIsPhysicalAverageGaugeCross
    background selected averageRow =
  trans
    (selectedSchurCrossTransposeIsAverageDefectCross
      background (Split.gaugeMultiplier selected) averageRow)
    (sym (DefectOnly.averageGaugeCrossDefectOnly
      background selected averageRow))

selectedSchurCrossMatrixSameObjectLevel : ProofLevel
selectedSchurCrossMatrixSameObjectLevel = machineChecked

selectedSchurFlatCrossVanishingLevel : ProofLevel
selectedSchurFlatCrossVanishingLevel = machineChecked

selectedSchurPhysicalCrossActionLevel : ProofLevel
selectedSchurPhysicalCrossActionLevel = machineChecked
