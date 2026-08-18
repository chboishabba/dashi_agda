module DASHI.Physics.YangMills.BalabanSelectedSchurGaugeGreenTwoSidedContractionExact where

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
-- Complement the selected Schur residual row estimate by the exact column
-- estimate required by the repository's finite l1 reopening theorem.  The
-- Schur perturbation
--
--   Q_A = E_A - (1/256) C_A C_A^T
--
-- is symmetric: E_A is a difference of Gram matrices and the finite-rank
-- correction is a scaled C_A C_A^T product.  The flat Fourier Green G_0 is
-- symmetric as well.  Therefore
--
--   (G_0 Q_A)(i,j) = (Q_A G_0)(j,i).
--
-- The already-proved row bounds
--
--   rowMass(Q_A) <= 7449/65536,
--   rowMass(G_0) <= 17/16
--
-- give the reverse-product row mass and hence the forward-product column mass
--
--   columnMass(G_0 Q_A)
--     <= 126633/1048576 < 1/8 < 1/6.
--
-- Thus the SAME physical Schur residual contracts both l-infinity and l1.
-- This is the missing finite input for constructing the rational inverse of
-- I + G_0 Q_A without an infinite-series completeness assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteColumnMassExact as ColumnMass
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact as Neumann
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramFiniteRangeExact as GaugeGram
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact as Perturbation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Flat
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact as FlatTwoSided
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeGreenAbsoluteMassExact as GreenMass
import DASHI.Physics.YangMills.BalabanSelectedSchurCrossAbsoluteMassExact as Cross
import DASHI.Physics.YangMills.BalabanSelectedSchurFiniteRankCorrectionExact as Correction
import DASHI.Physics.YangMills.BalabanSelectedSchurGaugeGreenContractionExact as Schur
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeRow : Set
GaugeRow = Cross.GaugeRow

gaugeGramSymmetric : ∀ background left right →
  GaugeGram.selectedBackgroundGaugeGram background left right
  ≡ GaugeGram.selectedBackgroundGaugeGram background right left
gaugeGramSymmetric background left right =
  Sums.sumRationalCong Flat.gaugeRows _ _
    (λ column → ℚP.*-comm
      (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
        background left column)
      (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
        background right column))

perturbationSymmetric : ∀ background left right →
  Perturbation.gaugeGramPerturbationMatrix background left right
  ≡ Perturbation.gaugeGramPerturbationMatrix background right left
perturbationSymmetric background left right =
  cong₂ _-_
    (gaugeGramSymmetric background left right)
    (gaugeGramSymmetric Physical.identityBackground left right)

rawCorrectionSymmetric : ∀ background left right →
  Correction.rawSchurCorrection background left right
  ≡ Correction.rawSchurCorrection background right left
rawCorrectionSymmetric background left right =
  ColumnMass.transposeProductSwapExact
    Cross.averageRows
    (Cross.selectedSchurCrossMatrix background)
    (Cross.selectedSchurCrossMatrix background)
    left right

correctionSymmetric : ∀ background left right →
  Correction.selectedSchurFiniteRankCorrection background left right
  ≡ Correction.selectedSchurFiniteRankCorrection background right left
correctionSymmetric background left right =
  cong (Correction.schurScale *_) (rawCorrectionSymmetric background left right)

schurPerturbationSymmetric : ∀ background left right →
  Schur.schurPerturbation background left right
  ≡ Schur.schurPerturbation background right left
schurPerturbationSymmetric background left right =
  cong₂ _-_
    (perturbationSymmetric background left right)
    (correctionSymmetric background left right)

reverseSchurResidual :
  Physical.RationalSU2Background4 → GaugeRow → GaugeRow → ℚ
reverseSchurResidual background =
  Matrix.matrixProduct Cross.gaugeRows
    (Schur.schurPerturbation background)
    Flat.flatGreenKernelMatrix

schurResidualTransposeExact : ∀ background left right →
  Schur.flatGreenTimesSchurPerturbation background left right
  ≡ reverseSchurResidual background right left
schurResidualTransposeExact background left right =
  Sums.sumRationalCong Cross.gaugeRows _ _
    (λ middle →
      trans
        (cong
          (Flat.flatGreenKernelMatrix left middle *_)
          (schurPerturbationSymmetric background middle right))
        (trans
          (ℚP.*-comm
            (Flat.flatGreenKernelMatrix left middle)
            (Schur.schurPerturbation background right middle))
          (cong
            (Schur.schurPerturbation background right middle *_)
            (FlatTwoSided.flatGreenKernelSymmetric left middle))))

reverseSchurResidualRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Neumann.rowMass Cross.gaugeRows (reverseSchurResidual background) row
  ≤ Schur.schurGreenContractionBound
reverseSchurResidualRowMassBound background radius row =
  let
    raw = Neumann.productRowMassBound
      Cross.gaugeRows
      (Schur.schurPerturbation background)
      Flat.flatGreenKernelMatrix
      Schur.schurPerturbationRowMassBound
      GreenMass.seventeenSixteenths
      (ℚP.nonNegative⁻¹ GreenMass.seventeenSixteenths)
      (Schur.selectedSchurPerturbationRowMassBound background radius)
      Flat.selectedFlatGaugeGreenAbsoluteRowMassBound
      row

    coefficientExact :
      Schur.schurPerturbationRowMassBound * GreenMass.seventeenSixteenths
      ≡ Schur.schurGreenContractionBound
    coefficientExact = ℚRing.solve []
  in
  subst
    (λ upper →
      Neumann.rowMass Cross.gaugeRows (reverseSchurResidual background) row
      ≤ upper)
    coefficientExact raw

schurResidualColumnMassAsReverseRowMass : ∀ background column →
  ColumnMass.squareColumnMass Cross.gaugeRows
    (Schur.flatGreenTimesSchurPerturbation background) column
  ≡ Neumann.rowMass Cross.gaugeRows (reverseSchurResidual background) column
schurResidualColumnMassAsReverseRowMass background column =
  Sums.sumRationalCong Cross.gaugeRows _ _
    (λ row → cong ∣_∣ (schurResidualTransposeExact background row column))

selectedSchurResidualAbsoluteColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  ColumnMass.squareColumnMass Cross.gaugeRows
    (Schur.flatGreenTimesSchurPerturbation background) column
  ≤ Schur.schurGreenContractionBound
selectedSchurResidualAbsoluteColumnMassBound background radius column =
  subst
    (λ lower → lower ≤ Schur.schurGreenContractionBound)
    (sym (schurResidualColumnMassAsReverseRowMass background column))
    (reverseSchurResidualRowMassBound background radius column)

selectedSchurResidualColumnOneEighthContraction :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  ColumnMass.squareColumnMass Cross.gaugeRows
    (Schur.flatGreenTimesSchurPerturbation background) column
  ≤ Schur.oneEighth
selectedSchurResidualColumnOneEighthContraction background radius column =
  ℚP.≤-trans
    (selectedSchurResidualAbsoluteColumnMassBound background radius column)
    Schur.schurGreenContractionBelowOneEighth

selectedSchurGaugeGreenTwoSidedContractionLevel : ProofLevel
selectedSchurGaugeGreenTwoSidedContractionLevel = machineChecked
