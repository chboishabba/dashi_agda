module DASHI.Physics.YangMills.BalabanClayT4GeneratedGridMeasureOrbitExact where

------------------------------------------------------------------------
-- METHOD / PHYSICAL CONTEXT
--
-- Stefano Capitani,
-- "Lattice Perturbation Theory", Physics Reports 382 (2003), 113--302.
-- DOI: 10.1016/S0370-1573(03)00211-4.  arXiv: hep-lat/0211036.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The generated normalized Brillouin partition uses the four equal-width
-- intervals [-1,-1/2],[-1/2,0],[0,1/2],[1/2,1].  Therefore every one of the
-- 4^4 cells has exactly the same normalized Lebesgue volume (1/2)^4 = 1/16.
-- This proves that the orbit multiplicities 64,96,64,16 (or the conservative
-- seven fixed-axis multiplicities) need no additional orbit-dependent measure
-- weight.  Sign flips and coordinate permutations preserve the exact box
-- volume on the literal generated GridCell4 carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _-_; _*_ ; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact as Orbit

half sixteenth : ℚ
half = + 1 / 2
sixteenth = + 1 / 16

intervalWidth : Integral.RationalInterval → ℚ
intervalWidth interval = Integral.upper interval - Integral.lower interval

generatedIntervalWidth : Grid.IntervalCell → ℚ
generatedIntervalWidth cell = intervalWidth (Grid.cellInterval cell)

allGeneratedIntervalsHaveWidthHalf : ∀ cell →
  generatedIntervalWidth cell ≡ half
allGeneratedIntervalsHaveWidthHalf Grid.negativeOuter = refl
allGeneratedIntervalsHaveWidthHalf Grid.negativeInner = refl
allGeneratedIntervalsHaveWidthHalf Grid.positiveInner = refl
allGeneratedIntervalsHaveWidthHalf Grid.positiveOuter = refl

normalizedBoxVolume : Integral.MomentumBox4 → ℚ
normalizedBoxVolume box =
  intervalWidth (Integral.k0 box) *
  intervalWidth (Integral.k1 box) *
  intervalWidth (Integral.k2 box) *
  intervalWidth (Integral.k3 box)

generatedCellVolume : Grid.GridCell4 → ℚ
generatedCellVolume cell = normalizedBoxVolume (Grid.asMomentumBox cell)

allGeneratedCellsHaveVolumeSixteenth : ∀ cell →
  generatedCellVolume cell ≡ sixteenth
allGeneratedCellsHaveVolumeSixteenth (Grid.gridCell4 a b c d)
  rewrite allGeneratedIntervalsHaveWidthHalf a
        | allGeneratedIntervalsHaveWidthHalf b
        | allGeneratedIntervalsHaveWidthHalf c
        | allGeneratedIntervalsHaveWidthHalf d = refl

hyperoctahedralGeneratorPreservesGeneratedCellVolume :
  ∀ generator cell →
  generatedCellVolume (Orbit.act generator cell) ≡ generatedCellVolume cell
hyperoctahedralGeneratorPreservesGeneratedCellVolume generator cell
  rewrite allGeneratedCellsHaveVolumeSixteenth (Orbit.act generator cell)
        | allGeneratedCellsHaveVolumeSixteenth cell = refl

-- Weighted orbit totals in normalized-cube measure.  The equal-cell-volume
-- theorem makes the usual integer orbit multiplicities literally sufficient.
rank1NormalizedVolume : ℚ
rank1NormalizedVolume = (+ 64 / 1) * sixteenth
rank2NormalizedVolume : ℚ
rank2NormalizedVolume = (+ 96 / 1) * sixteenth
rank3NormalizedVolume : ℚ
rank3NormalizedVolume = (+ 64 / 1) * sixteenth
rank4NormalizedVolume : ℚ
rank4NormalizedVolume = (+ 16 / 1) * sixteenth

regularNormalizedVolume : ℚ
regularNormalizedVolume =
  rank1NormalizedVolume + rank2NormalizedVolume +
  rank3NormalizedVolume + rank4NormalizedVolume

regularNormalizedVolumeExact : regularNormalizedVolume ≡ + 15 / 1
regularNormalizedVolumeExact = refl

infraredNormalizedVolume : ℚ
infraredNormalizedVolume = (+ 16 / 1) * sixteenth

infraredNormalizedVolumeExact : infraredNormalizedVolume ≡ + 1 / 1
infraredNormalizedVolumeExact = refl

fullNormalizedCubeVolumeExact :
  infraredNormalizedVolume + regularNormalizedVolume ≡ + 16 / 1
fullNormalizedCubeVolumeExact = refl

generatedGridEqualCellMeasureLevel : ProofLevel
generatedGridEqualCellMeasureLevel = machineChecked

hyperoctahedralGeneratedMeasureInvarianceLevel : ProofLevel
hyperoctahedralGeneratedMeasureInvarianceLevel = machineChecked
