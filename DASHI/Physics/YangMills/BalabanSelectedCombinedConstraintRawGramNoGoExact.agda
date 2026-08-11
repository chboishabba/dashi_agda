module DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRawGramNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
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
-- Close a dangerous route before it can infect the physical tangent theorem.
-- The literal 780-row combined constraint contains all 768 gauge rows.  At the
-- identity background, a constant gauge multiplier is annihilated by the
-- actual gauge adjoint because that adjoint is the negative periodic gradient.
-- Setting all twelve block-average multiplier coordinates to zero therefore
-- gives a NONZERO multiplier in the kernel of the full raw combined Gram.
--
-- Hence the raw matrix
--
--      L_0 L_0^* : Q^780 -> Q^780
--
-- has no two-sided inverse.  Any universal tangent projector must first remove
-- the gauge redundancy (for example on a based/reduced carrier) or use a
-- stratum-aware quotient/pseudoinverse.  A bare full-780-row inverse is not a
-- legitimate Gate-I producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (pair; map; _++_)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintFiniteKKTExact as KKT
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageRowCarrierExact as AverageRows
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint

SelectedMultiplier : Set
SelectedMultiplier = KKT.SelectedMultiplierVector

unitGaugeMultiplier : FlatAdjoint.GaugeMultiplier
unitGaugeMultiplier _ = 1ℚ

rawFlatRedundancyMultiplier : SelectedMultiplier
rawFlatRedundancyMultiplier (Combined.averageConstraintRow _) = 0ℚ
rawFlatRedundancyMultiplier (Combined.gaugeConstraintRow _) = 1ℚ

zeroSelectedMultiplier : SelectedMultiplier
zeroSelectedMultiplier _ = 0ℚ

rawFlatRedundancyGaugeCoordinateExact : ∀ gaugeRow →
  rawFlatRedundancyMultiplier (Combined.gaugeConstraintRow gaugeRow) ≡ 1ℚ
rawFlatRedundancyGaugeCoordinateExact gaugeRow = refl

constantGaugeForwardDifferenceZero : ∀ axis site →
  Periodic.forwardDifference axis
    (FlatAdjoint.multiplierField unitGaugeMultiplier Coordinates.coordinateX) site
  ≡ 0ℚ
constantGaugeForwardDifferenceZero axis site = ℚRing.solve []

actualFlatGaugeAdjointUnitZero : ∀ stateCoordinate →
  FlatAdjoint.actualFlatGaugeAdjoint unitGaugeMultiplier stateCoordinate ≡ 0ℚ
actualFlatGaugeAdjointUnitZero
    (pair coordinate (pair axis site)) =
  trans
    (FlatAdjoint.actualFlatGaugeAdjointPointwiseExact
      unitGaugeMultiplier (pair coordinate (pair axis site)))
    (ℚRing.solve [])

sumZero : ∀ {A : Set} (values : Agda.Builtin.List.List A) →
  Sums.sumRational values (λ _ → 0ℚ) ≡ 0ℚ
sumZero [] = refl
sumZero (_ ∷ values) rewrite sumZero values = refl

averageTransposePartZero : ∀ stateCoordinate →
  Sums.sumRational
    (map Combined.averageConstraintRow
      (Rows.Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector))
    (λ row →
      Rect.transposeRectangular
        (Combined.selectedBackgroundLinearizedConstraintMatrix
          Physical.identityBackground)
        stateCoordinate row
      * rawFlatRedundancyMultiplier row)
  ≡ 0ℚ
averageTransposePartZero stateCoordinate =
  trans
    (Fubini.sumRationalMap
      Combined.averageConstraintRow
      (Rows.Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
      (λ row →
        Rect.transposeRectangular
          (Combined.selectedBackgroundLinearizedConstraintMatrix
            Physical.identityBackground)
          stateCoordinate row
        * rawFlatRedundancyMultiplier row))
    (trans
      (Sums.sumRationalCong
        (Rows.Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
        _ (λ _ → 0ℚ)
        (λ row → ℚRing.solve-∀
          (Combined.selectedBackgroundLinearizedConstraintMatrix
            Physical.identityBackground
            (Combined.averageConstraintRow row) stateCoordinate)))
      (sumZero
        (Rows.Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)))

gaugeTransposePartEqualsFlatAdjoint : ∀ stateCoordinate →
  Sums.sumRational
    (map Combined.gaugeConstraintRow
      (Rows.Basis.elements Rows.selectedGaugeRowFiniteSelector))
    (λ row →
      Rect.transposeRectangular
        (Combined.selectedBackgroundLinearizedConstraintMatrix
          Physical.identityBackground)
        stateCoordinate row
      * rawFlatRedundancyMultiplier row)
  ≡ FlatAdjoint.actualFlatGaugeAdjoint unitGaugeMultiplier stateCoordinate
gaugeTransposePartEqualsFlatAdjoint stateCoordinate =
  trans
    (Fubini.sumRationalMap
      Combined.gaugeConstraintRow
      (Rows.Basis.elements Rows.selectedGaugeRowFiniteSelector)
      (λ row →
        Rect.transposeRectangular
          (Combined.selectedBackgroundLinearizedConstraintMatrix
            Physical.identityBackground)
          stateCoordinate row
        * rawFlatRedundancyMultiplier row))
    (Sums.sumRationalCong
      (Rows.Basis.elements Rows.selectedGaugeRowFiniteSelector)
      _ _
      (λ gaugeRow → refl))

rawFlatRedundancyTransposeZero : ∀ stateCoordinate →
  KKT.selectedCombinedConstraintTransposeApply
    Physical.identityBackground rawFlatRedundancyMultiplier stateCoordinate
  ≡ 0ℚ
rawFlatRedundancyTransposeZero stateCoordinate =
  trans
    (Fubini.sumRationalAppend
      (map Combined.averageConstraintRow
        (Rows.Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector))
      (map Combined.gaugeConstraintRow
        (Rows.Basis.elements Rows.selectedGaugeRowFiniteSelector))
      (λ row →
        Rect.transposeRectangular
          (Combined.selectedBackgroundLinearizedConstraintMatrix
            Physical.identityBackground)
          stateCoordinate row
        * rawFlatRedundancyMultiplier row))
    (trans
      (cong₂ _+_
        (averageTransposePartZero stateCoordinate)
        (gaugeTransposePartEqualsFlatAdjoint stateCoordinate))
      (trans
        (cong (0ℚ +_)
          (actualFlatGaugeAdjointUnitZero stateCoordinate))
        (ℚRing.solve [])))
  where
  open import Relation.Binary.PropositionalEquality using (cong₂)

combinedConstraintOfZeroState : ∀ row →
  Combined.selectedBackgroundCombinedConstraintApply Physical.identityBackground
    (λ _ → 0ℚ) row
  ≡ 0ℚ
combinedConstraintOfZeroState row =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates
        DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact.physicalStateCarrier)
      _ (λ _ → 0ℚ)
      (λ coordinate → ℚRing.solve-∀
        (Combined.selectedBackgroundLinearizedConstraintMatrix
          Physical.identityBackground row coordinate)))
    (sumZero
      (Matrix.coordinates
        DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact.physicalStateCarrier))

rawFlatRedundancyGramZero : ∀ row →
  KKT.selectedCombinedConstraintGramApply
    Physical.identityBackground rawFlatRedundancyMultiplier row
  ≡ 0ℚ
rawFlatRedundancyGramZero row =
  trans
    (KKT.selectedCombinedConstraintGramActionExact
      Physical.identityBackground rawFlatRedundancyMultiplier row)
    (trans
      (CombinedConstraintRespectsPointwise row)
      (combinedConstraintOfZeroState row))
  where
  CombinedConstraintRespectsPointwise : ∀ row →
    Combined.selectedBackgroundCombinedConstraintApply Physical.identityBackground
      (KKT.selectedCombinedConstraintTransposeApply
        Physical.identityBackground rawFlatRedundancyMultiplier) row
    ≡ Combined.selectedBackgroundCombinedConstraintApply Physical.identityBackground
      (λ _ → 0ℚ) row
  CombinedConstraintRespectsPointwise selected =
    Sums.sumRationalCong
      (Matrix.coordinates
        DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact.physicalStateCarrier)
      _ _
      (λ coordinate →
        cong
          (Combined.selectedBackgroundLinearizedConstraintMatrix
            Physical.identityBackground selected coordinate *_)
          (rawFlatRedundancyTransposeZero coordinate))

rawFlatRedundancyNotZero :
  ∀ site → ¬ (∀ row → rawFlatRedundancyMultiplier row ≡ zeroSelectedMultiplier row)
rawFlatRedundancyNotZero site allZero =
  let
    selected = Combined.gaugeConstraintRow (pair Coordinates.coordinateX site)
    oneEqualsZero : 1ℚ ≡ 0ℚ
    oneEqualsZero = allZero selected
    zeroLessOne : 0ℚ < 1ℚ
    zeroLessOne = toWitness {a? = 0ℚ ℚP.<? 1ℚ} _
    impossible : 0ℚ < 0ℚ
    impossible = subst (λ value → 0ℚ < value) oneEqualsZero zeroLessOne
  in
  ℚP.<-irrefl 0ℚ impossible

matrixApplyRespectsPointwise :
  ∀ {Index : Set}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    (matrix : Matrix.RationalMatrix Index)
    left right →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ row →
  Matrix.applyMatrix carrier matrix left row
  ≡ Matrix.applyMatrix carrier matrix right row
matrixApplyRespectsPointwise carrier matrix left right pointwise row =
  Sums.sumRationalCong (Matrix.coordinates carrier) _ _
    (λ coordinate → cong (matrix row coordinate *_) (pointwise coordinate))

matrixApplyZero :
  ∀ {Index : Set}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    (matrix : Matrix.RationalMatrix Index) row →
  Matrix.applyMatrix carrier matrix (λ _ → 0ℚ) row ≡ 0ℚ
matrixApplyZero carrier matrix row =
  trans
    (Sums.sumRationalCong (Matrix.coordinates carrier) _ (λ _ → 0ℚ)
      (λ coordinate → ℚRing.solve-∀ (matrix row coordinate)))
    (sumZero (Matrix.coordinates carrier))

rawCombinedFlatGramHasNoTwoSidedInverse :
  ∀ site →
  ¬ Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (Combined.selectedBackgroundConstraintGram Physical.identityBackground)
rawCombinedFlatGramHasNoTwoSidedInverse site certificate =
  let
    inverse = Matrix.inverseMatrix certificate
    selected = Combined.gaugeConstraintRow (pair Coordinates.coordinateX site)

    gramSource = KKT.selectedCombinedConstraintGramApply
      Physical.identityBackground rawFlatRedundancyMultiplier

    gramZero : ∀ row → gramSource row ≡ zeroSelectedMultiplier row
    gramZero row = rawFlatRedundancyGramZero row

    inverseCong :
      Matrix.applyMatrix Rows.selectedCombinedConstraintRowCarrier
        inverse gramSource selected
      ≡ Matrix.applyMatrix Rows.selectedCombinedConstraintRowCarrier
        inverse zeroSelectedMultiplier selected
    inverseCong = matrixApplyRespectsPointwise
      Rows.selectedCombinedConstraintRowCarrier inverse
      gramSource zeroSelectedMultiplier gramZero selected

    inverseZero :
      Matrix.applyMatrix Rows.selectedCombinedConstraintRowCarrier
        inverse zeroSelectedMultiplier selected ≡ 0ℚ
    inverseZero = matrixApplyZero
      Rows.selectedCombinedConstraintRowCarrier inverse selected

    leftInverse :
      Matrix.applyMatrix Rows.selectedCombinedConstraintRowCarrier
        inverse gramSource selected
      ≡ rawFlatRedundancyMultiplier selected
    leftInverse = Matrix.matrixInverseLeftExact
      certificate rawFlatRedundancyMultiplier selected

    oneEqualsZero : 1ℚ ≡ 0ℚ
    oneEqualsZero = trans (sym leftInverse) (trans inverseCong inverseZero)

    zeroLessOne : 0ℚ < 1ℚ
    zeroLessOne = toWitness {a? = 0ℚ ℚP.<? 1ℚ} _
    impossible : 0ℚ < 0ℚ
    impossible = subst (λ value → 0ℚ < value) oneEqualsZero zeroLessOne
  in
  ℚP.<-irrefl 0ℚ impossible

selectedRawCombinedGramKernelNoGoLevel : ProofLevel
selectedRawCombinedGramKernelNoGoLevel = machineChecked

selectedRawCombinedGramInvertibilityNoGoLevel : ProofLevel
selectedRawCombinedGramInvertibilityNoGoLevel = machineChecked
