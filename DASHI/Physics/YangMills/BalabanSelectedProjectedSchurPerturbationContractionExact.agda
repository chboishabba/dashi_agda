module DASHI.Physics.YangMills.BalabanSelectedProjectedSchurPerturbationContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrodinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
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
-- Correct the unprojected Schur contraction to the actual mean-zero quotient
-- used by the selected reduced combined normal operator.  Away from the flat
-- background the gauge Gram need not preserve the flat constant-mode
-- complement, so the physical reduced Schur perturbation is
--
--       Q_A^red = P_g Q_A,
--
-- where P_g is the literal componentwise centering projection and
--
--       Q_A = E_A - (1/256) C_A C_A^T.
--
-- The preceding exact absolute-mass bounds are
--
--       ||P_g||_{row,col} <= 2,
--       ||Q_A||_{row,col} <= 7449/65536.
--
-- Hence
--
--       ||Q_A^red||_{row,col} <= 7449/32768.
--
-- Preconditioning by the exact flat Fourier Green gives
--
--       R_A^red = G_0 Q_A^red,
--       ||R_A^red||_{row,col}
--         <= (17/16)(7449/32768)
--          = 126633/524288
--          < 1/4.
--
-- The existing finite growth-weight envelope 1 <= w <= 6561/4096 then gives
--
--       sum_y |R_A^red(x,y)| w(y)
--         <= [830839113/2147483648] w(x)
--         < (2/5) w(x) < (1/2) w(x).
--
-- This is the strict contraction on the SAME projected Schur operator required
-- by the physical reduced quotient.  It replaces the earlier unprojected
-- shortcut without reopening any 780-row Combes--Thomas analysis.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _<_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteColumnMassExact as ColumnMass
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact as Neumann
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedRowSumContractionExact as WeightedRow
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFiniteRationalReopeningExact as Carrier
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact as Scale
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Flat
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact as FlatTwoSided
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeGreenAbsoluteMassExact as GreenMass
import DASHI.Physics.YangMills.BalabanSelectedGaugeCenteringProjectionMassExact as Center
import DASHI.Physics.YangMills.BalabanSelectedSchurCrossAbsoluteMassExact as Cross
import DASHI.Physics.YangMills.BalabanSelectedSchurGaugeGreenContractionExact as Schur
import DASHI.Physics.YangMills.BalabanSelectedSchurGaugeGreenTwoSidedContractionExact as TwoSided
import DASHI.Physics.YangMills.BalabanSelectedSchurPerturbationActionExact as SchurAction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalCombesThomasWeightExact as Weight
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalCombesThomasWeightEnvelopeExact as Envelope
import DASHI.Physics.YangMills.BalabanFiniteWeightEnvelopeRowPromotionExact as Promote
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeRow : Set
GaugeRow = Cross.GaugeRow

GaugeMultiplier : Set
GaugeMultiplier = GaugeRow → ℚ

gaugeRows = Cross.gaugeRows

------------------------------------------------------------------------
-- Projected Schur perturbation P_g Q_A.
------------------------------------------------------------------------

projectedSchurPerturbation :
  Physical.RationalSU2Background4 → GaugeRow → GaugeRow → ℚ
projectedSchurPerturbation background =
  Matrix.matrixProduct gaugeRows
    Center.gaugeCenteringProjectionMatrix
    (Schur.schurPerturbation background)

projectedSchurPerturbationBound : ℚ
projectedSchurPerturbationBound = + 7449 / 32768

projectedSchurPerturbationBoundExact :
  Center.centeringProjectionRowMassBound
    * Schur.schurPerturbationRowMassBound
  ≡ projectedSchurPerturbationBound
projectedSchurPerturbationBoundExact = ℚRing.solve []

selectedProjectedSchurPerturbationRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Neumann.rowMass gaugeRows (projectedSchurPerturbation background) row
  ≤ projectedSchurPerturbationBound
selectedProjectedSchurPerturbationRowMassBound background radius row =
  let
    raw = Neumann.productRowMassBound
      gaugeRows
      Center.gaugeCenteringProjectionMatrix
      (Schur.schurPerturbation background)
      Center.centeringProjectionRowMassBound
      Schur.schurPerturbationRowMassBound
      (ℚP.nonNegative⁻¹ Schur.schurPerturbationRowMassBound)
      Center.gaugeCenteringProjectionAbsoluteRowMassBound
      (Schur.selectedSchurPerturbationRowMassBound background radius)
      row
  in
  subst
    (λ upper →
      Neumann.rowMass gaugeRows (projectedSchurPerturbation background) row
      ≤ upper)
    projectedSchurPerturbationBoundExact raw

schurPerturbationColumnMassAsRowMass : ∀ background column →
  ColumnMass.squareColumnMass gaugeRows
    (Schur.schurPerturbation background) column
  ≡ Neumann.rowMass gaugeRows (Schur.schurPerturbation background) column
schurPerturbationColumnMassAsRowMass background column =
  Sums.sumRationalCong gaugeRows _ _
    (λ row → cong ∣_∣
      (TwoSided.schurPerturbationSymmetric background row column))

selectedSchurPerturbationColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  ColumnMass.squareColumnMass gaugeRows
    (Schur.schurPerturbation background) column
  ≤ Schur.schurPerturbationRowMassBound
selectedSchurPerturbationColumnMassBound background radius column =
  subst
    (λ lower → lower ≤ Schur.schurPerturbationRowMassBound)
    (sym (schurPerturbationColumnMassAsRowMass background column))
    (Schur.selectedSchurPerturbationRowMassBound background radius column)

transposeSchurPerturbation :
  Physical.RationalSU2Background4 → GaugeRow → GaugeRow → ℚ
transposeSchurPerturbation background row column =
  Schur.schurPerturbation background column row

projectedSchurAsTransposeProduct : ∀ background row column →
  projectedSchurPerturbation background row column
  ≡ Mass.transposeProduct gaugeRows
      Center.gaugeCenteringProjectionMatrix
      (transposeSchurPerturbation background)
      row column
projectedSchurAsTransposeProduct background row column = refl

transposeSchurRowMassAsColumnMass : ∀ background row →
  Mass.absoluteRectRowMass gaugeRows
    (transposeSchurPerturbation background) row
  ≡ ColumnMass.squareColumnMass gaugeRows
      (Schur.schurPerturbation background) row
transposeSchurRowMassAsColumnMass background row = refl

selectedProjectedSchurPerturbationColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  ColumnMass.squareColumnMass gaugeRows
    (projectedSchurPerturbation background) column
  ≤ projectedSchurPerturbationBound
selectedProjectedSchurPerturbationColumnMassBound background radius column =
  let
    raw :
      ColumnMass.squareColumnMass gaugeRows
        (Mass.transposeProduct gaugeRows
          Center.gaugeCenteringProjectionMatrix
          (transposeSchurPerturbation background)) column
      ≤ Mass.absoluteRectRowMass gaugeRows
          (transposeSchurPerturbation background) column
          * Center.centeringProjectionRowMassBound
    raw = ColumnMass.transposeProductColumnMassBound
      gaugeRows gaugeRows
      Center.gaugeCenteringProjectionMatrix
      (transposeSchurPerturbation background)
      Center.centeringProjectionRowMassBound column
      (ℚP.nonNegative⁻¹ Center.centeringProjectionRowMassBound)
      Center.gaugeCenteringProjectionAbsoluteColumnMassBound

    rightBound :
      Mass.absoluteRectRowMass gaugeRows
          (transposeSchurPerturbation background) column
          * Center.centeringProjectionRowMassBound
      ≤ Schur.schurPerturbationRowMassBound
          * Center.centeringProjectionRowMassBound
    rightBound = Scale.rightScaleMonotone
      Center.centeringProjectionRowMassBound
      (Mass.absoluteRectRowMass gaugeRows
        (transposeSchurPerturbation background) column)
      Schur.schurPerturbationRowMassBound
      (ℚP.nonNegative⁻¹ Center.centeringProjectionRowMassBound)
      (subst
        (λ lower → lower ≤ Schur.schurPerturbationRowMassBound)
        (sym (transposeSchurRowMassAsColumnMass background column))
        (selectedSchurPerturbationColumnMassBound background radius column))

    productExact :
      Schur.schurPerturbationRowMassBound
        * Center.centeringProjectionRowMassBound
      ≡ projectedSchurPerturbationBound
    productExact = ℚRing.solve []

    identify :
      ColumnMass.squareColumnMass gaugeRows
        (projectedSchurPerturbation background) column
      ≡ ColumnMass.squareColumnMass gaugeRows
          (Mass.transposeProduct gaugeRows
            Center.gaugeCenteringProjectionMatrix
            (transposeSchurPerturbation background)) column
    identify = Sums.sumRationalCong gaugeRows _ _
      (λ row → cong ∣_∣
        (projectedSchurAsTransposeProduct background row column))
  in
  subst
    (λ lower → lower ≤ projectedSchurPerturbationBound)
    (sym identify)
    (ℚP.≤-trans raw
      (subst
        (λ upper →
          Mass.absoluteRectRowMass gaugeRows
            (transposeSchurPerturbation background) column
            * Center.centeringProjectionRowMassBound
          ≤ upper)
        productExact rightBound))

------------------------------------------------------------------------
-- Exact action is P_g(Q_A v) = centeredMultiplier(Q_A v).
------------------------------------------------------------------------

projectedSchurAsRectangularCompose : ∀ background row column →
  projectedSchurPerturbation background row column
  ≡ Rect.composeRectangular Carrier.gaugeFiniteCoordinates
      Center.gaugeCenteringProjectionMatrix
      (Schur.schurPerturbation background)
      row column
projectedSchurAsRectangularCompose background row column = refl

projectedSchurPerturbationApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
projectedSchurPerturbationApply background =
  Rect.applyRectangular Carrier.gaugeFiniteCoordinates
    (projectedSchurPerturbation background)

projectedSchurPerturbationActionExact :
  ∀ background multiplier row →
  projectedSchurPerturbationApply background multiplier row
  ≡ Mean.centeredMultiplier
      (SchurAction.schurPerturbationApply background multiplier) row
projectedSchurPerturbationActionExact background multiplier row =
  let
    identify :
      projectedSchurPerturbationApply background multiplier row
      ≡ Rect.applyRectangular Carrier.gaugeFiniteCoordinates
          (Rect.composeRectangular Carrier.gaugeFiniteCoordinates
            Center.gaugeCenteringProjectionMatrix
            (Schur.schurPerturbation background))
          multiplier row
    identify = Sums.sumRationalCong gaugeRows _ _
      (λ column → cong (_* multiplier column)
        (projectedSchurAsRectangularCompose background row column))
  in
  trans identify
    (trans
      (Rect.applyComposeRectangularExact
        Carrier.gaugeFiniteCoordinates
        Carrier.gaugeFiniteCoordinates
        Center.gaugeCenteringProjectionMatrix
        (Schur.schurPerturbation background)
        multiplier row)
      (Center.gaugeCenteringProjectionActionExact
        (SchurAction.schurPerturbationApply background multiplier) row))

------------------------------------------------------------------------
-- Flat Green preconditioning.
------------------------------------------------------------------------

projectedSchurResidual :
  Physical.RationalSU2Background4 → GaugeRow → GaugeRow → ℚ
projectedSchurResidual background =
  Matrix.matrixProduct gaugeRows
    Flat.flatGreenKernelMatrix
    (projectedSchurPerturbation background)

projectedSchurResidualBound : ℚ
projectedSchurResidualBound = + 126633 / 524288

projectedSchurResidualBoundExact :
  GreenMass.seventeenSixteenths * projectedSchurPerturbationBound
  ≡ projectedSchurResidualBound
projectedSchurResidualBoundExact = ℚRing.solve []

selectedProjectedSchurResidualRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Neumann.rowMass gaugeRows (projectedSchurResidual background) row
  ≤ projectedSchurResidualBound
selectedProjectedSchurResidualRowMassBound background radius row =
  let
    raw = Neumann.productRowMassBound
      gaugeRows
      Flat.flatGreenKernelMatrix
      (projectedSchurPerturbation background)
      GreenMass.seventeenSixteenths
      projectedSchurPerturbationBound
      (ℚP.nonNegative⁻¹ projectedSchurPerturbationBound)
      Flat.selectedFlatGaugeGreenAbsoluteRowMassBound
      (selectedProjectedSchurPerturbationRowMassBound background radius)
      row
  in
  subst
    (λ upper →
      Neumann.rowMass gaugeRows (projectedSchurResidual background) row ≤ upper)
    projectedSchurResidualBoundExact raw

transposeProjectedSchur :
  Physical.RationalSU2Background4 → GaugeRow → GaugeRow → ℚ
transposeProjectedSchur background row column =
  projectedSchurPerturbation background column row

projectedSchurResidualAsTransposeProduct : ∀ background row column →
  projectedSchurResidual background row column
  ≡ Mass.transposeProduct gaugeRows
      Flat.flatGreenKernelMatrix
      (transposeProjectedSchur background)
      row column
projectedSchurResidualAsTransposeProduct background row column = refl

transposeProjectedSchurRowMassAsColumnMass : ∀ background row →
  Mass.absoluteRectRowMass gaugeRows
    (transposeProjectedSchur background) row
  ≡ ColumnMass.squareColumnMass gaugeRows
      (projectedSchurPerturbation background) row
transposeProjectedSchurRowMassAsColumnMass background row = refl

selectedProjectedSchurResidualColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  ColumnMass.squareColumnMass gaugeRows
    (projectedSchurResidual background) column
  ≤ projectedSchurResidualBound
selectedProjectedSchurResidualColumnMassBound background radius column =
  let
    raw :
      ColumnMass.squareColumnMass gaugeRows
        (Mass.transposeProduct gaugeRows
          Flat.flatGreenKernelMatrix
          (transposeProjectedSchur background)) column
      ≤ Mass.absoluteRectRowMass gaugeRows
          (transposeProjectedSchur background) column
          * GreenMass.seventeenSixteenths
    raw = ColumnMass.transposeProductColumnMassBound
      gaugeRows gaugeRows
      Flat.flatGreenKernelMatrix
      (transposeProjectedSchur background)
      GreenMass.seventeenSixteenths column
      (ℚP.nonNegative⁻¹ GreenMass.seventeenSixteenths)
      FlatTwoSided.selectedFlatGaugeGreenAbsoluteColumnMassBound

    rightBound :
      Mass.absoluteRectRowMass gaugeRows
          (transposeProjectedSchur background) column
          * GreenMass.seventeenSixteenths
      ≤ projectedSchurPerturbationBound * GreenMass.seventeenSixteenths
    rightBound = Scale.rightScaleMonotone
      GreenMass.seventeenSixteenths
      (Mass.absoluteRectRowMass gaugeRows
        (transposeProjectedSchur background) column)
      projectedSchurPerturbationBound
      (ℚP.nonNegative⁻¹ GreenMass.seventeenSixteenths)
      (subst
        (λ lower → lower ≤ projectedSchurPerturbationBound)
        (sym (transposeProjectedSchurRowMassAsColumnMass background column))
        (selectedProjectedSchurPerturbationColumnMassBound
          background radius column))

    productExact :
      projectedSchurPerturbationBound * GreenMass.seventeenSixteenths
      ≡ projectedSchurResidualBound
    productExact = ℚRing.solve []

    identify :
      ColumnMass.squareColumnMass gaugeRows
        (projectedSchurResidual background) column
      ≡ ColumnMass.squareColumnMass gaugeRows
          (Mass.transposeProduct gaugeRows
            Flat.flatGreenKernelMatrix
            (transposeProjectedSchur background)) column
    identify = Sums.sumRationalCong gaugeRows _ _
      (λ row → cong ∣_∣
        (projectedSchurResidualAsTransposeProduct background row column))
  in
  subst
    (λ lower → lower ≤ projectedSchurResidualBound)
    (sym identify)
    (ℚP.≤-trans raw
      (subst
        (λ upper →
          Mass.absoluteRectRowMass gaugeRows
            (transposeProjectedSchur background) column
            * GreenMass.seventeenSixteenths
          ≤ upper)
        productExact rightBound))

projectedSchurResidualBelowOneQuarter :
  projectedSchurResidualBound < + 1 / 4
projectedSchurResidualBelowOneQuarter = toWitness _

------------------------------------------------------------------------
-- Weighted contraction survives the physical quotient projection.
------------------------------------------------------------------------

weightedProjectedSchurResidualBound : ℚ
weightedProjectedSchurResidualBound = + 830839113 / 2147483648

weightedProjectedSchurResidualBoundExact :
  Weight.siteGrowthEnvelope * projectedSchurResidualBound
  ≡ weightedProjectedSchurResidualBound
weightedProjectedSchurResidualBoundExact = ℚRing.solve []

weightedProjectedSchurResidualBelowTwoFifths :
  weightedProjectedSchurResidualBound < + 2 / 5
weightedProjectedSchurResidualBelowTwoFifths = toWitness _

weightedProjectedSchurResidualBelowOneHalf :
  weightedProjectedSchurResidualBound < + 1 / 2
weightedProjectedSchurResidualBelowOneHalf = toWitness _

selectedProjectedSchurResidualWeightedRowBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root left →
  WeightedRow.weightedRowSum gaugeRows
    (projectedSchurResidual background)
    (Weight.gaugeInverseWeight root) left
  ≤ weightedProjectedSchurResidualBound
      * Weight.gaugeInverseWeight root left
selectedProjectedSchurResidualWeightedRowBound background radius root left =
  let
    raw = Promote.boundedWeightPromotesUniformRow
      gaugeRows
      (projectedSchurResidual background)
      (Weight.gaugeInverseWeight root)
      Weight.siteGrowthEnvelope
      projectedSchurResidualBound
      (ℚP.nonNegative⁻¹ Weight.siteGrowthEnvelope)
      (ℚP.nonNegative⁻¹ projectedSchurResidualBound)
      (Envelope.gaugeInverseWeightAboveOne root)
      (Weight.gaugeInverseWeightBelowEnvelope root)
      (selectedProjectedSchurResidualRowMassBound background radius)
      left
  in
  subst
    (λ factor →
      WeightedRow.weightedRowSum gaugeRows
        (projectedSchurResidual background)
        (Weight.gaugeInverseWeight root) left
      ≤ factor * Weight.gaugeInverseWeight root left)
    weightedProjectedSchurResidualBoundExact raw

selectedProjectedSchurPerturbationMassLevel : ProofLevel
selectedProjectedSchurPerturbationMassLevel = machineChecked

selectedProjectedSchurResidualTwoSidedLevel : ProofLevel
selectedProjectedSchurResidualTwoSidedLevel = machineChecked

selectedProjectedSchurResidualWeightedLevel : ProofLevel
selectedProjectedSchurResidualWeightedLevel = machineChecked
