module DASHI.Physics.YangMills.BalabanSelectedProjectedPaddedSchurReducedSameObjectExact where

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
-- Remove the regularization ambiguity from the projected Schur Green on the
-- actual selected reduced multiplier carrier.  The flat reference inverse is
-- implemented for
--
--   K_0^reg = K_0 + P_const,
--
-- while the selected combined multiplier quotient stores a proof that every
-- gauge component is globally mean zero.  Hence P_const vanishes pointwise on
-- that carrier and the padded projected Schur operator is literally
--
--   K_0 + P_g Q_A,
--
-- not merely a comparison operator.  Combining this with the already-proved
-- projected-action theorem identifies the correction with the centered
-- physical Schur perturbation used by the 12 + 765 block elimination.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen
import DASHI.Physics.YangMills.BalabanSelectedProjectedSchurPerturbationContractionExact as Projected
import DASHI.Physics.YangMills.BalabanSelectedProjectedSchurGreenFiniteExact as SchurGreen
import DASHI.Physics.YangMills.BalabanSelectedSchurPerturbationActionExact as SchurAction
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean

flatGaugeMeanProjectorReducedZero :
  ∀ multiplier →
  FlatFloor.FlatGaugeReducedMultiplier multiplier →
  ∀ coordinate site →
  FlatGreen.flatGaugeMeanProjector multiplier (Torus.pair coordinate site)
  ≡ 0ℚ
flatGaugeMeanProjectorReducedZero multiplier reduced Coordinates.coordinateX site =
  FlatFloor.coordinateXMeanZero reduced site
flatGaugeMeanProjectorReducedZero multiplier reduced Coordinates.coordinateY site =
  FlatFloor.coordinateYMeanZero reduced site
flatGaugeMeanProjectorReducedZero multiplier reduced Coordinates.coordinateZ site =
  FlatFloor.coordinateZMeanZero reduced site

regularizedFlatGaugeGramReducedSameObject :
  ∀ multiplier →
  FlatFloor.FlatGaugeReducedMultiplier multiplier →
  ∀ coordinate site →
  FlatGreen.regularizedFlatGaugeGramApply multiplier
    (Torus.pair coordinate site)
  ≡ FlatGreen.flatGaugeGramApply multiplier (Torus.pair coordinate site)
regularizedFlatGaugeGramReducedSameObject multiplier reduced coordinate site =
  trans
    (cong
      (FlatGreen.flatGaugeGramApply multiplier (Torus.pair coordinate site) +_)
      (flatGaugeMeanProjectorReducedZero multiplier reduced coordinate site))
    (ℚRing.solve-∀
      (FlatGreen.flatGaugeGramApply multiplier (Torus.pair coordinate site)))

projectedPaddedSchurReducedSameObject :
  ∀ background multiplier →
  FlatFloor.FlatGaugeReducedMultiplier multiplier →
  ∀ coordinate site →
  SchurGreen.projectedPaddedSchurApply background multiplier
    (Torus.pair coordinate site)
  ≡ FlatGreen.flatGaugeGramApply multiplier (Torus.pair coordinate site)
    + Projected.projectedSchurPerturbationApply background multiplier
        (Torus.pair coordinate site)
projectedPaddedSchurReducedSameObject
    background multiplier reduced coordinate site =
  cong
    (_+ Projected.projectedSchurPerturbationApply background multiplier
          (Torus.pair coordinate site))
    (regularizedFlatGaugeGramReducedSameObject
      multiplier reduced coordinate site)

projectedPaddedSchurReducedPhysicalActionExact :
  ∀ background multiplier →
  FlatFloor.FlatGaugeReducedMultiplier multiplier →
  ∀ coordinate site →
  SchurGreen.projectedPaddedSchurApply background multiplier
    (Torus.pair coordinate site)
  ≡ FlatGreen.flatGaugeGramApply multiplier (Torus.pair coordinate site)
    + Mean.centeredMultiplier
        (SchurAction.schurPerturbationApply background multiplier)
        (Torus.pair coordinate site)
projectedPaddedSchurReducedPhysicalActionExact
    background multiplier reduced coordinate site =
  trans
    (projectedPaddedSchurReducedSameObject
      background multiplier reduced coordinate site)
    (cong
      (FlatGreen.flatGaugeGramApply multiplier
        (Torus.pair coordinate site) +_)
      (Projected.projectedSchurPerturbationActionExact
        background multiplier (Torus.pair coordinate site)))

selectedProjectedPaddedSchurReducedSameObjectLevel : ProofLevel
selectedProjectedPaddedSchurReducedSameObjectLevel = machineChecked
