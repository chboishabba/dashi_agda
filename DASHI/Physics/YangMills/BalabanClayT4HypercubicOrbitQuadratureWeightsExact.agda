module DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitQuadratureWeightsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I.", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The generated normalized Brillouin partition cuts every coordinate interval
-- [-1,1] into four cells of width 1/2.  Thus every four-dimensional cell has
-- normalized volume (1/2)^4 = 1/16.  Combining this with the proved regular
-- orbit multiplicities 64,96,64,16 gives exact joint quadrature weights
--
--             4, 6, 4, 1.
--
-- The missing all-inner orbit has 16 cells and volume 1, so regular volume is
-- 15 and total normalized cube volume is 16.  These are geometric/Jacobian
-- weights only; any physical k = pi q coordinate normalization remains a
-- separate semantic factor and does not block the normalized beta evaluation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _*_; _+_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

half cellVolume : ℚ
half = + 1 / 2
cellVolume = half * half * half * half

oneOuterMultiplicity twoOuterMultiplicity
  threeOuterMultiplicity fourOuterMultiplicity infraredMultiplicity : ℚ
oneOuterMultiplicity = + 64 / 1
twoOuterMultiplicity = + 96 / 1
threeOuterMultiplicity = + 64 / 1
fourOuterMultiplicity = + 16 / 1
infraredMultiplicity = + 16 / 1

oneOuterWeight twoOuterWeight threeOuterWeight fourOuterWeight infraredWeight : ℚ
oneOuterWeight = oneOuterMultiplicity * cellVolume
twoOuterWeight = twoOuterMultiplicity * cellVolume
threeOuterWeight = threeOuterMultiplicity * cellVolume
fourOuterWeight = fourOuterMultiplicity * cellVolume
infraredWeight = infraredMultiplicity * cellVolume

cellVolumeIsOneSixteenth : cellVolume ≡ + 1 / 16
cellVolumeIsOneSixteenth = ℚRing.solve-∀

oneOuterWeightIsFour : oneOuterWeight ≡ + 4 / 1
oneOuterWeightIsFour = ℚRing.solve-∀

twoOuterWeightIsSix : twoOuterWeight ≡ + 6 / 1
twoOuterWeightIsSix = ℚRing.solve-∀

threeOuterWeightIsFour : threeOuterWeight ≡ + 4 / 1
threeOuterWeightIsFour = ℚRing.solve-∀

fourOuterWeightIsOne : fourOuterWeight ≡ + 1 / 1
fourOuterWeightIsOne = ℚRing.solve-∀

infraredWeightIsOne : infraredWeight ≡ + 1 / 1
infraredWeightIsOne = ℚRing.solve-∀

regularNormalizedVolume : ℚ
regularNormalizedVolume =
  oneOuterWeight + twoOuterWeight + threeOuterWeight + fourOuterWeight

totalNormalizedVolume : ℚ
totalNormalizedVolume = regularNormalizedVolume + infraredWeight

regularNormalizedVolumeIsFifteen : regularNormalizedVolume ≡ + 15 / 1
regularNormalizedVolumeIsFifteen = ℚRing.solve-∀

totalNormalizedVolumeIsSixteen : totalNormalizedVolume ≡ + 16 / 1
totalNormalizedVolumeIsSixteen = ℚRing.solve-∀

-- Joint four-orbit weighted combination used by the normalized quadrature
-- consumer.  The expressions themselves can preserve all within-orbit
-- cancellations before any lower enclosure is taken.
weightedFourOrbitCombination : ℚ → ℚ → ℚ → ℚ → ℚ
weightedFourOrbitCombination one two three four =
  oneOuterWeight * one
  + twoOuterWeight * two
  + threeOuterWeight * three
  + fourOuterWeight * four

weightedFourOrbitCombinationCanonical : ∀ one two three four →
  weightedFourOrbitCombination one two three four
  ≡ (+ 4 / 1) * one
    + (+ 6 / 1) * two
    + (+ 4 / 1) * three
    + four
weightedFourOrbitCombinationCanonical one two three four =
  ℚRing.solve-∀ one two three four

hypercubicOrbitQuadratureWeightLevel : ProofLevel
hypercubicOrbitQuadratureWeightLevel = machineChecked
