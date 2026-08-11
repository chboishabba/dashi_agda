module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationActionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- The selected-background Green lane had two descriptions of E_A:
--
--   (1) the literal finite matrix K_A-K_0 used by the absolute-mass estimates;
--   (2) the three-term operator expression used by the exact decomposition
--       K_A^reg = K_0^reg + E_A.
--
-- This module proves they are the SAME vector action.  It first identifies the
-- actual Gram matrix L_A L_A^T with the already-used background gauge-Gram
-- operator, then subtracts the identity-background action.  Thus the later
-- finite reopening inverse acts on the exact operator decomposition, not on a
-- merely comparable matrix.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact as Difference
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramFiniteRangeExact as Gram
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact as Perturbation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeReducedFloorExact as BackgroundFloor
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeOperatorDecompositionExact as Operator

GaugeMultiplier : Set
GaugeMultiplier = FlatAdjoint.GaugeMultiplier

selectedGaugeGramMatrixApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
selectedGaugeGramMatrixApply background =
  Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
    (Gram.selectedBackgroundGaugeGram background)

selectedGaugeGramMatrixActionExact :
  ∀ background multiplier row →
  selectedGaugeGramMatrixApply background multiplier row
  ≡ Operator.backgroundGaugeGramApply background multiplier row
selectedGaugeGramMatrixActionExact background multiplier row =
  Rect.applyComposeRectangularExact
    KKT.physicalStateCarrier
    FlatAdjoint.selectedFlatGaugeRowCarrier
    (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background)
    (Rect.transposeRectangular
      (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background))
    multiplier row

identityGaugeGramMatrixActionExact :
  ∀ multiplier row →
  selectedGaugeGramMatrixApply Physical.identityBackground multiplier row
  ≡ FlatGreen.flatGaugeGramApply multiplier row
identityGaugeGramMatrixActionExact multiplier row = refl

selectedGaugeGramPerturbationApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
selectedGaugeGramPerturbationApply background =
  Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
    (Perturbation.gaugeGramPerturbationMatrix background)

selectedGaugeGramPerturbationDifferenceExact :
  ∀ background multiplier row →
  selectedGaugeGramPerturbationApply background multiplier row
  ≡ selectedGaugeGramMatrixApply background multiplier row
    - selectedGaugeGramMatrixApply Physical.identityBackground multiplier row
selectedGaugeGramPerturbationDifferenceExact background multiplier row =
  let
    rows = Rect.Matrix.coordinates FlatAdjoint.selectedFlatGaugeRowCarrier
    backgroundGram = Gram.selectedBackgroundGaugeGram background
    flatGram = Gram.selectedBackgroundGaugeGram Physical.identityBackground

    pointwise : ∀ column →
      (backgroundGram row column - flatGram row column) * multiplier column
      ≡ backgroundGram row column * multiplier column
        - flatGram row column * multiplier column
    pointwise column = ℚRing.solve-∀
      (backgroundGram row column)
      (flatGram row column)
      (multiplier column)
  in
  trans
    (Sums.sumRationalCong rows _ _ pointwise)
    (Difference.sumSubtract rows
      (λ column → backgroundGram row column * multiplier column)
      (λ column → flatGram row column * multiplier column))

selectedGaugeGramPerturbationActsAsExplicitEA :
  ∀ background multiplier row →
  selectedGaugeGramPerturbationApply background multiplier row
  ≡ Operator.explicitGaugeGramPerturbation background multiplier row
selectedGaugeGramPerturbationActsAsExplicitEA background multiplier row =
  trans
    (selectedGaugeGramPerturbationDifferenceExact background multiplier row)
    (trans
      (cong₂ _-_
        (selectedGaugeGramMatrixActionExact background multiplier row)
        (identityGaugeGramMatrixActionExact multiplier row))
      (trans
        (cong
          (_- FlatGreen.flatGaugeGramApply multiplier row)
          (Operator.backgroundGaugeGramDecomposition background multiplier row))
        (ℚRing.solve-∀
          (FlatGreen.flatGaugeGramApply multiplier row)
          (Operator.explicitGaugeGramPerturbation background multiplier row))))
  where
    open import Relation.Binary.PropositionalEquality using (cong₂)

selectedGaugeGramMatrixActionLevel : ProofLevel
selectedGaugeGramMatrixActionLevel = machineChecked

selectedGaugeGramPerturbationActionLevel : ProofLevel
selectedGaugeGramPerturbationActionLevel = machineChecked
