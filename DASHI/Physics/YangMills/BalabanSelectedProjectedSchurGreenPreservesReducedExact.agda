module DASHI.Physics.YangMills.BalabanSelectedProjectedSchurGreenPreservesReducedExact where

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
-- Prove that the exact projected Schur Green already constructed on the padded
-- 768-coordinate gauge carrier restricts to the physical 765-dimensional
-- componentwise-mean-zero quotient.  No invariant-subspace premise is added.
-- The proof reads the constant mode directly from the exact Schur equation:
--
--   P_const (S~_A gamma) = P_const gamma.
--
-- Indeed K_0 gamma and P_g Q_A gamma are reduced, while the only constant
-- contribution in K_0^reg is P_const gamma itself.  Therefore a reduced source
-- and the exact right-inverse equation force the Schur solution to be reduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFiniteRationalReopeningExact as Carrier
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeGramPreservesReducedExact as FlatReduced
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean
import DASHI.Physics.YangMills.BalabanSelectedGaugeCenteringLinearityExact as Linear
import DASHI.Physics.YangMills.BalabanSelectedGaugeReducedLinearClosureExact as Reduced
import DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact as Split
import DASHI.Physics.YangMills.BalabanSelectedSchurPerturbationActionExact as SchurAction
import DASHI.Physics.YangMills.BalabanSelectedProjectedSchurPerturbationContractionExact as Projected
import DASHI.Physics.YangMills.BalabanSelectedProjectedSchurFiniteRationalReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanSelectedProjectedSchurGreenFiniteExact as SchurGreen

GaugeMultiplier : Set
GaugeMultiplier = FlatFloor.GaugeMultiplier

constantProjectionRespectsPointwise :
  ∀ {left right : GaugeMultiplier} →
  (∀ row → left row ≡ right row) →
  ∀ coordinate site →
  Mean.constantProjection left (Torus.pair coordinate site)
  ≡ Mean.constantProjection right (Torus.pair coordinate site)
constantProjectionRespectsPointwise {left} {right} pointwise coordinate site =
  cong (GlobalAverage.oneTwoFiftySix *_)
    (Periodic.sumSitesCong
      (FlatFloor.gaugeMultiplierField left coordinate)
      (FlatFloor.gaugeMultiplierField right coordinate)
      (λ current → pointwise (Torus.pair coordinate current)))

constantProjectionIdempotent :
  ∀ multiplier coordinate site →
  Mean.constantProjection (Mean.constantProjection multiplier)
    (Torus.pair coordinate site)
  ≡ Mean.constantProjection multiplier (Torus.pair coordinate site)
constantProjectionIdempotent multiplier coordinate site =
  let value = Mean.constantProjection multiplier (Torus.pair coordinate site)
  in trans
    (cong (GlobalAverage.oneTwoFiftySix *_)
      (Mean.siteSumConstantExact value))
    (ℚRing.solve-∀ value)

flatMeanProjectorIsConstantProjection :
  ∀ multiplier coordinate site →
  FlatGreen.flatGaugeMeanProjector multiplier (Torus.pair coordinate site)
  ≡ Mean.constantProjection multiplier (Torus.pair coordinate site)
flatMeanProjectorIsConstantProjection multiplier coordinate site =
  GlobalAverage.average0123EqualsGlobalMean
    (FlatFloor.gaugeMultiplierField multiplier coordinate) site

regularizedFlatGaugeGramConstantProjectionExact :
  ∀ multiplier coordinate site →
  Mean.constantProjection
    (FlatGreen.regularizedFlatGaugeGramApply multiplier)
    (Torus.pair coordinate site)
  ≡ Mean.constantProjection multiplier (Torus.pair coordinate site)
regularizedFlatGaugeGramConstantProjectionExact multiplier coordinate site =
  let
    flat = FlatGreen.flatGaugeGramApply multiplier
    constant = Mean.constantProjection multiplier
    split : ∀ row →
      FlatGreen.regularizedFlatGaugeGramApply multiplier row
      ≡ Linear.addMultiplier flat constant row
    split (Torus.pair c s) =
      cong (flat (Torus.pair c s) +_)
        (flatMeanProjectorIsConstantProjection multiplier c s)
  in
  trans
    (constantProjectionRespectsPointwise split coordinate site)
    (trans
      (Linear.constantProjectionAddExact flat constant coordinate site)
      (trans
        (cong
          (_+ Mean.constantProjection constant (Torus.pair coordinate site))
          (Split.constantProjectionReducedZero flat
            (FlatReduced.flatGaugeGramApplyReduced multiplier)
            coordinate site))
        (trans
          (cong (0ℚ +_)
            (constantProjectionIdempotent multiplier coordinate site))
          (ℚRing.solve-∀
            (Mean.constantProjection multiplier
              (Torus.pair coordinate site))))))

projectedSchurPerturbationReduced :
  ∀ background multiplier →
  FlatFloor.FlatGaugeReducedMultiplier
    (Projected.projectedSchurPerturbationApply background multiplier)
projectedSchurPerturbationReduced background multiplier =
  Reduced.meanZeroRespectsPointwise
    (Projected.projectedSchurPerturbationActionExact background multiplier)
    (Mean.centeredMultiplierReduced
      (SchurAction.schurPerturbationApply background multiplier))

projectedPaddedSchurConstantProjectionExact :
  ∀ background multiplier coordinate site →
  Mean.constantProjection
    (SchurGreen.projectedPaddedSchurApply background multiplier)
    (Torus.pair coordinate site)
  ≡ Mean.constantProjection multiplier (Torus.pair coordinate site)
projectedPaddedSchurConstantProjectionExact background multiplier coordinate site =
  let
    flat = FlatGreen.regularizedFlatGaugeGramApply multiplier
    perturbation = Projected.projectedSchurPerturbationApply background multiplier
    split : ∀ row →
      SchurGreen.projectedPaddedSchurApply background multiplier row
      ≡ Linear.addMultiplier flat perturbation row
    split row = refl
  in
  trans
    (constantProjectionRespectsPointwise split coordinate site)
    (trans
      (Linear.constantProjectionAddExact flat perturbation coordinate site)
      (trans
        (cong₂ _+_
          (regularizedFlatGaugeGramConstantProjectionExact
            multiplier coordinate site)
          (Split.constantProjectionReducedZero perturbation
            (projectedSchurPerturbationReduced background multiplier)
            coordinate site))
        (ℚRing.solve-∀
          (Mean.constantProjection multiplier
            (Torus.pair coordinate site)))))

constantProjectionZeroImpliesReduced :
  ∀ multiplier →
  (∀ coordinate site →
    Mean.constantProjection multiplier (Torus.pair coordinate site) ≡ 0ℚ) →
  FlatFloor.FlatGaugeReducedMultiplier multiplier
constantProjectionZeroImpliesReduced multiplier zero = record
  { FlatFloor.FlatGaugeReducedMultiplier.coordinateXMeanZero =
      close Coordinates.coordinateX
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateYMeanZero =
      close Coordinates.coordinateY
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateZMeanZero =
      close Coordinates.coordinateZ
  }
  where
  close : ∀ coordinate site →
    Path4.average0123
      (FlatFloor.gaugeMultiplierField multiplier coordinate) site ≡ 0ℚ
  close coordinate site =
    trans
      (GlobalAverage.average0123EqualsGlobalMean
        (FlatFloor.gaugeMultiplierField multiplier coordinate) site)
      (zero coordinate site)

selectedProjectedSchurGreenPreservesReduced :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Carrier.gaugeFiniteCoordinates
      (Reopen.projectedSchurIdentityPlusMatrix background))
    source →
  FlatFloor.FlatGaugeReducedMultiplier source →
  FlatFloor.FlatGaugeReducedMultiplier
    (SchurGreen.selectedProjectedSchurGreen background certificate source)
selectedProjectedSchurGreenPreservesReduced
    background certificate source sourceReduced =
  let
    solution = SchurGreen.selectedProjectedSchurGreen background certificate source
    schurEqualsSource : ∀ row →
      SchurGreen.projectedPaddedSchurApply background solution row ≡ source row
    schurEqualsSource =
      SchurGreen.selectedProjectedSchurGreenRightInverse
        background certificate source
    solutionConstantZero : ∀ coordinate site →
      Mean.constantProjection solution (Torus.pair coordinate site) ≡ 0ℚ
    solutionConstantZero coordinate site =
      trans
        (sym
          (projectedPaddedSchurConstantProjectionExact
            background solution coordinate site))
        (trans
          (constantProjectionRespectsPointwise schurEqualsSource coordinate site)
          (Split.constantProjectionReducedZero source sourceReduced
            coordinate site))
  in
  constantProjectionZeroImpliesReduced solution solutionConstantZero

selectedProjectedSchurConstantModeConservationLevel : ProofLevel
selectedProjectedSchurConstantModeConservationLevel = machineChecked

selectedProjectedSchurGreenPreservesReducedLevel : ProofLevel
selectedProjectedSchurGreenPreservesReducedLevel = machineChecked
