module DASHI.Physics.YangMills.BalabanSelectedSchurPerturbationActionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- Put the Schur-corrected perturbation on the same exact operator action as
-- the selected combined constraint block decomposition.  The kernel-level
-- object used by the absolute-mass estimates is
--
--   Q_A = E_A - F_A,
--   F_A = (1/256) C_A C_A^T.
--
-- This file proves its finite matrix action is exactly the physical gauge-Gram
-- perturbation action minus the literal finite-rank correction.  It then proves
-- the contraction kernel already bounded below 1/8 is exactly
--
--   R_A^Schur = G_0 Q_A
--
-- as an operator composition.  Thus the new two-sided/weighted contraction is
-- attached to the same Schur perturbation used in the block elimination.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact as Difference
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact as Perturbation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationActionExact as EAction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Flat
import DASHI.Physics.YangMills.BalabanSelectedSchurCrossAbsoluteMassExact as Cross
import DASHI.Physics.YangMills.BalabanSelectedSchurFiniteRankCorrectionExact as Correction
import DASHI.Physics.YangMills.BalabanSelectedSchurGaugeGreenContractionExact as Schur
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical

GaugeMultiplier : Set
GaugeMultiplier = FlatAdjoint.GaugeMultiplier

schurCorrectionApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
schurCorrectionApply background =
  Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
    (Correction.selectedSchurFiniteRankCorrection background)

schurPerturbationApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
schurPerturbationApply background =
  Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
    (Schur.schurPerturbation background)

schurPerturbationApplyDifferenceExact :
  ∀ background multiplier row →
  schurPerturbationApply background multiplier row
  ≡ EAction.selectedGaugeGramPerturbationApply background multiplier row
    - schurCorrectionApply background multiplier row
schurPerturbationApplyDifferenceExact background multiplier row =
  let
    rows = Cross.gaugeRows
    E = Perturbation.gaugeGramPerturbationMatrix background
    F = Correction.selectedSchurFiniteRankCorrection background

    pointwise : ∀ column →
      (E row column - F row column) * multiplier column
      ≡ E row column * multiplier column
        - F row column * multiplier column
    pointwise column = ℚRing.solve-∀
      (E row column) (F row column) (multiplier column)
  in
  trans
    (Sums.sumRationalCong rows _ _ pointwise)
    (Difference.sumSubtract rows
      (λ column → E row column * multiplier column)
      (λ column → F row column * multiplier column))

schurResidualKernelIsRectangularCompose : ∀ background row column →
  Schur.flatGreenTimesSchurPerturbation background row column
  ≡ Rect.composeRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
      Flat.flatGreenKernelMatrix
      (Schur.schurPerturbation background)
      row column
schurResidualKernelIsRectangularCompose background row column = refl

schurResidualApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
schurResidualApply background =
  Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
    (Schur.flatGreenTimesSchurPerturbation background)

schurResidualApplyAsFlatGreenQ :
  ∀ background multiplier row →
  schurResidualApply background multiplier row
  ≡ FlatGreen.regularizedFlatGaugeGreen
      (schurPerturbationApply background multiplier) row
schurResidualApplyAsFlatGreenQ background multiplier row =
  let
    composeAction =
      Rect.applyComposeRectangularExact
        FlatAdjoint.selectedFlatGaugeRowCarrier
        FlatAdjoint.selectedFlatGaugeRowCarrier
        Flat.flatGreenKernelMatrix
        (Schur.schurPerturbation background)
        multiplier row

    kernelActs : ∀ selected →
      Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
        Flat.flatGreenKernelMatrix
        (schurPerturbationApply background multiplier) selected
      ≡ FlatGreen.regularizedFlatGaugeGreen
          (schurPerturbationApply background multiplier) selected
    kernelActs (Torus.pair coordinate site) =
      Flat.flatGreenKernelActsExactly
        (schurPerturbationApply background multiplier) coordinate site
  in
  trans
    (Sums.sumRationalCong Cross.gaugeRows _ _
      (λ column →
        cong (_* multiplier column)
          (schurResidualKernelIsRectangularCompose background row column)))
    (trans composeAction (kernelActs row))

selectedSchurPerturbationActionLevel : ProofLevel
selectedSchurPerturbationActionLevel = machineChecked

selectedSchurResidualSameObjectLevel : ProofLevel
selectedSchurResidualSameObjectLevel = machineChecked
