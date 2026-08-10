module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeOperatorDecompositionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01215223.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- Expand the literal selected-background gauge Gram around the actual flat
-- selected matrix.  Writing
--
--   L_A = L_0 + D_A,
--   L_A^* = L_0^* + D_A^*,
--
-- the finite matrix calculation gives, pointwise on the 768-row multiplier
-- carrier,
--
--   K_A = L_A L_A^*
--       = K_0 + L_0 D_A^* + D_A L_0^* + D_A D_A^*.
--
-- Adding the same flat constant projector to both sides yields the exact
-- anchor identity
--
--   K_A^reg = K_0^reg + E_A,
--
-- where K_0^reg is *literally* the operator already inverted by the explicit
-- side-four Fourier Green kernel.  E_A is the displayed three-term physical
-- perturbation, not an opaque difference supplied by a caller.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as Defect
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeReducedFloorExact as BackgroundFloor
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen

GaugeMultiplier : Set
GaugeMultiplier = FlatAdjoint.GaugeMultiplier

backgroundGaugeConstraintApply :
  Physical.RationalSU2Background4 → KKT.StateVector → GaugeMultiplier
backgroundGaugeConstraintApply background =
  Rect.applyRectangular KKT.physicalStateCarrier
    (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background)

flatGaugeConstraintApply : KKT.StateVector → GaugeMultiplier
flatGaugeConstraintApply = FlatAdjoint.identityGaugeConstraintApply

gaugeDefectForwardApply :
  Physical.RationalSU2Background4 → KKT.StateVector → GaugeMultiplier
gaugeDefectForwardApply background state row =
  Sums.sumRational Coordinates.physicalSU2Coordinates4
    (λ selected → Defect.gaugeDefectMatrix background row selected * state selected)

backgroundGaugeConstraintSplits :
  ∀ background state row →
  backgroundGaugeConstraintApply background state row
  ≡ flatGaugeConstraintApply state row
    + gaugeDefectForwardApply background state row
backgroundGaugeConstraintSplits background state row =
  let
    pointwise : ∀ selected →
      GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected
        * state selected
      ≡ GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
          Physical.identityBackground row selected * state selected
        + Defect.gaugeDefectMatrix background row selected * state selected
    pointwise selected =
      ℚRing.solve-∀
        (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected)
        (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
          Physical.identityBackground row selected)
        (state selected)
  in
  trans
    (Sums.sumRationalCong Coordinates.physicalSU2Coordinates4 _ _ pointwise)
    (BackgroundFloor.sumRationalAddExact Coordinates.physicalSU2Coordinates4
      (λ selected →
        GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
          Physical.identityBackground row selected * state selected)
      (λ selected →
        Defect.gaugeDefectMatrix background row selected * state selected))

backgroundGaugeConstraintAdd :
  ∀ background left right row →
  backgroundGaugeConstraintApply background (Rect.vectorAdd left right) row
  ≡ backgroundGaugeConstraintApply background left row
    + backgroundGaugeConstraintApply background right row
backgroundGaugeConstraintAdd background left right row =
  let
    pointwise : ∀ selected →
      GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected
        * Rect.vectorAdd left right selected
      ≡ GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected
        * left selected
        + GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected
        * right selected
    pointwise selected =
      ℚRing.solve-∀
        (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected)
        (left selected) (right selected)
  in
  trans
    (Sums.sumRationalCong Coordinates.physicalSU2Coordinates4 _ _ pointwise)
    (BackgroundFloor.sumRationalAddExact Coordinates.physicalSU2Coordinates4
      (λ selected →
        GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected
        * left selected)
      (λ selected →
        GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected
        * right selected))

backgroundGaugeGramApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
backgroundGaugeGramApply background multiplier =
  backgroundGaugeConstraintApply background
    (BackgroundFloor.backgroundGaugeAdjoint background multiplier)

flatGaugeGramApply : GaugeMultiplier → GaugeMultiplier
flatGaugeGramApply = FlatGreen.flatGaugeGramApply

explicitGaugeGramPerturbation :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
explicitGaugeGramPerturbation background multiplier row =
  flatGaugeConstraintApply
      (Defect.gaugeAdjointDefectApply background multiplier) row
  + gaugeDefectForwardApply background
      (FlatAdjoint.actualFlatGaugeAdjoint multiplier) row
  + gaugeDefectForwardApply background
      (Defect.gaugeAdjointDefectApply background multiplier) row

backgroundGaugeGramDecomposition :
  ∀ background multiplier row →
  backgroundGaugeGramApply background multiplier row
  ≡ flatGaugeGramApply multiplier row
    + explicitGaugeGramPerturbation background multiplier row
backgroundGaugeGramDecomposition background multiplier row =
  let
    flatAdjoint = FlatAdjoint.actualFlatGaugeAdjoint multiplier
    defectAdjoint = Defect.gaugeAdjointDefectApply background multiplier

    replaceAdjoint :
      backgroundGaugeGramApply background multiplier row
      ≡ backgroundGaugeConstraintApply background
          (Rect.vectorAdd flatAdjoint defectAdjoint) row
    replaceAdjoint =
      cong
        (λ state → backgroundGaugeConstraintApply background state row)
        (λ selected → BackgroundFloor.backgroundGaugeAdjointSplits
          background multiplier selected)

    splitInput :
      backgroundGaugeConstraintApply background
          (Rect.vectorAdd flatAdjoint defectAdjoint) row
      ≡ backgroundGaugeConstraintApply background flatAdjoint row
        + backgroundGaugeConstraintApply background defectAdjoint row
    splitInput = backgroundGaugeConstraintAdd
      background flatAdjoint defectAdjoint row

    splitFlatInput :
      backgroundGaugeConstraintApply background flatAdjoint row
      ≡ flatGaugeConstraintApply flatAdjoint row
        + gaugeDefectForwardApply background flatAdjoint row
    splitFlatInput = backgroundGaugeConstraintSplits background flatAdjoint row

    splitDefectInput :
      backgroundGaugeConstraintApply background defectAdjoint row
      ≡ flatGaugeConstraintApply defectAdjoint row
        + gaugeDefectForwardApply background defectAdjoint row
    splitDefectInput = backgroundGaugeConstraintSplits background defectAdjoint row
  in
  trans replaceAdjoint
    (trans splitInput
      (trans
        (cong
          (λ rightTerm →
            backgroundGaugeConstraintApply background flatAdjoint row + rightTerm)
          splitDefectInput)
        (trans
          (cong
            (λ leftTerm →
              leftTerm
              + (flatGaugeConstraintApply defectAdjoint row
                + gaugeDefectForwardApply background defectAdjoint row))
            splitFlatInput)
          (ℚRing.solve-∀
            (flatGaugeConstraintApply flatAdjoint row)
            (flatGaugeConstraintApply defectAdjoint row)
            (gaugeDefectForwardApply background flatAdjoint row)
            (gaugeDefectForwardApply background defectAdjoint row))))))

constantProjectionMatchesFlatMeanProjector :
  ∀ multiplier coordinate site →
  Mean.constantProjection multiplier (pair coordinate site)
  ≡ FlatGreen.flatGaugeMeanProjector multiplier (pair coordinate site)
constantProjectionMatchesFlatMeanProjector multiplier coordinate site =
  sym
    (GlobalAverage.average0123EqualsGlobalMean
      (FlatAdjoint.multiplierField multiplier coordinate) site)

regularizedBackgroundGaugeGramApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
regularizedBackgroundGaugeGramApply background multiplier row =
  backgroundGaugeGramApply background multiplier row
  + Mean.constantProjection multiplier row

regularizedFlatAnchorMatchesExisting :
  ∀ multiplier coordinate site →
  flatGaugeGramApply multiplier (pair coordinate site)
    + Mean.constantProjection multiplier (pair coordinate site)
  ≡ FlatGreen.regularizedFlatGaugeGramApply multiplier (pair coordinate site)
regularizedFlatAnchorMatchesExisting multiplier coordinate site =
  cong
    (flatGaugeGramApply multiplier (pair coordinate site) +_)
    (constantProjectionMatchesFlatMeanProjector multiplier coordinate site)

selectedBackgroundBasedGaugeOperatorDecomposition :
  ∀ background multiplier coordinate site →
  regularizedBackgroundGaugeGramApply background multiplier
    (pair coordinate site)
  ≡ FlatGreen.regularizedFlatGaugeGramApply multiplier (pair coordinate site)
    + explicitGaugeGramPerturbation background multiplier (pair coordinate site)
selectedBackgroundBasedGaugeOperatorDecomposition
    background multiplier coordinate site =
  let
    row = pair coordinate site
    raw = backgroundGaugeGramDecomposition background multiplier row
    meanMatch = constantProjectionMatchesFlatMeanProjector multiplier coordinate site
  in
  trans
    (cong (_+ Mean.constantProjection multiplier row) raw)
    (trans
      (cong
        (λ meanValue →
          (flatGaugeGramApply multiplier row
            + explicitGaugeGramPerturbation background multiplier row)
          + meanValue)
        meanMatch)
      (ℚRing.solve-∀
        (flatGaugeGramApply multiplier row)
        (FlatGreen.flatGaugeMeanProjector multiplier row)
        (explicitGaugeGramPerturbation background multiplier row)))

selectedBackgroundGaugeOperatorDecompositionLevel : ProofLevel
selectedBackgroundGaugeOperatorDecompositionLevel = machineChecked

selectedBackgroundFlatGreenAnchorLevel : ProofLevel
selectedBackgroundFlatGreenAnchorLevel = machineChecked
