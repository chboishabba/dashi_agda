module DASHI.Physics.YangMills.BalabanSelectedGaugeCenteringLinearityExact where

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
-- DASHI CONTRIBUTION
--
-- Make the componentwise mean-zero projector algebra explicit on the literal
-- selected gauge multiplier carrier.  The Schur reconstruction needs to move
-- centering through sums, differences and rational scales while retaining the
-- exact finite side-four global mean used by the quotient presentation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean

GaugeMultiplier : Set
GaugeMultiplier = FlatFloor.GaugeMultiplier

addMultiplier : GaugeMultiplier → GaugeMultiplier → GaugeMultiplier
addMultiplier left right row = left row + right row

subtractMultiplier : GaugeMultiplier → GaugeMultiplier → GaugeMultiplier
subtractMultiplier left right row = left row - right row

scaleMultiplier : ℚ → GaugeMultiplier → GaugeMultiplier
scaleMultiplier coefficient multiplier row = coefficient * multiplier row

constantProjectionAddExact :
  ∀ left right coordinate site →
  Mean.constantProjection (addMultiplier left right)
    (Torus.pair coordinate site)
  ≡ Mean.constantProjection left (Torus.pair coordinate site)
    + Mean.constantProjection right (Torus.pair coordinate site)
constantProjectionAddExact left right coordinate site =
  let
    leftField = FlatFloor.gaugeMultiplierField left coordinate
    rightField = FlatFloor.gaugeMultiplierField right coordinate
  in
  trans
    (cong (GlobalAverage.oneTwoFiftySix *_)
      (Periodic.sumSitesAdd leftField rightField))
    (ℚRing.solve-∀
      (Periodic.sumSites leftField)
      (Periodic.sumSites rightField))

constantProjectionSubtractExact :
  ∀ left right coordinate site →
  Mean.constantProjection (subtractMultiplier left right)
    (Torus.pair coordinate site)
  ≡ Mean.constantProjection left (Torus.pair coordinate site)
    - Mean.constantProjection right (Torus.pair coordinate site)
constantProjectionSubtractExact left right coordinate site =
  let
    leftField = FlatFloor.gaugeMultiplierField left coordinate
    rightField = FlatFloor.gaugeMultiplierField right coordinate
  in
  trans
    (cong (GlobalAverage.oneTwoFiftySix *_)
      (Periodic.sumSitesSubtract leftField rightField))
    (ℚRing.solve-∀
      (Periodic.sumSites leftField)
      (Periodic.sumSites rightField))

constantProjectionScaleExact :
  ∀ coefficient multiplier coordinate site →
  Mean.constantProjection (scaleMultiplier coefficient multiplier)
    (Torus.pair coordinate site)
  ≡ coefficient
    * Mean.constantProjection multiplier (Torus.pair coordinate site)
constantProjectionScaleExact coefficient multiplier coordinate site =
  let field = FlatFloor.gaugeMultiplierField multiplier coordinate
  in
  trans
    (cong (GlobalAverage.oneTwoFiftySix *_)
      (Periodic.sumSitesScale coefficient field))
    (ℚRing.solve-∀ coefficient (Periodic.sumSites field))

centeredMultiplierAddExact :
  ∀ left right coordinate site →
  Mean.centeredMultiplier (addMultiplier left right)
    (Torus.pair coordinate site)
  ≡ Mean.centeredMultiplier left (Torus.pair coordinate site)
    + Mean.centeredMultiplier right (Torus.pair coordinate site)
centeredMultiplierAddExact left right coordinate site =
  trans
    (cong
      (addMultiplier left right (Torus.pair coordinate site) -_)
      (constantProjectionAddExact left right coordinate site))
    (ℚRing.solve-∀
      (left (Torus.pair coordinate site))
      (right (Torus.pair coordinate site))
      (Mean.constantProjection left (Torus.pair coordinate site))
      (Mean.constantProjection right (Torus.pair coordinate site)))

centeredMultiplierSubtractExact :
  ∀ left right coordinate site →
  Mean.centeredMultiplier (subtractMultiplier left right)
    (Torus.pair coordinate site)
  ≡ Mean.centeredMultiplier left (Torus.pair coordinate site)
    - Mean.centeredMultiplier right (Torus.pair coordinate site)
centeredMultiplierSubtractExact left right coordinate site =
  trans
    (cong
      (subtractMultiplier left right (Torus.pair coordinate site) -_)
      (constantProjectionSubtractExact left right coordinate site))
    (ℚRing.solve-∀
      (left (Torus.pair coordinate site))
      (right (Torus.pair coordinate site))
      (Mean.constantProjection left (Torus.pair coordinate site))
      (Mean.constantProjection right (Torus.pair coordinate site)))

centeredMultiplierScaleExact :
  ∀ coefficient multiplier coordinate site →
  Mean.centeredMultiplier (scaleMultiplier coefficient multiplier)
    (Torus.pair coordinate site)
  ≡ coefficient
    * Mean.centeredMultiplier multiplier (Torus.pair coordinate site)
centeredMultiplierScaleExact coefficient multiplier coordinate site =
  trans
    (cong
      (scaleMultiplier coefficient multiplier (Torus.pair coordinate site) -_)
      (constantProjectionScaleExact coefficient multiplier coordinate site))
    (ℚRing.solve-∀
      coefficient
      (multiplier (Torus.pair coordinate site))
      (Mean.constantProjection multiplier (Torus.pair coordinate site)))

selectedGaugeCenteringLinearityLevel : ProofLevel
selectedGaugeCenteringLinearityLevel = machineChecked
