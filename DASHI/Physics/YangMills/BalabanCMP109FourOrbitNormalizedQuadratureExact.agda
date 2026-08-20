module DASHI.Physics.YangMills.BalabanCMP109FourOrbitNormalizedQuadratureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
-- Direct source locators: Euclidean covariance (5.6),(5.7), beta extraction
-- (5.36)--(5.42).
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Compose the source symmetry and generated-grid finite geometry into the
-- exact normalized quadrature identity the beta calculation should consume.
-- If one cell contribution c(B) is the scalar projection of the literal CMP109
-- vacuum-polarization integrand and therefore obeys source (5.6),(5.7), then
--
--   (1/16) sum_(B regular) c(B)
--       = 4 c(B1) + 6 c(B2) + 4 c(B3) + c(B4),
--
-- where Bm is the canonical positive-sign cell with m outer coordinates.
-- Thus the 240-cell regular computation has exactly FOUR normalized scalar
-- values before quadrature error.  This theorem neither assumes positivity nor
-- interval bounds for those values.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _*_; _+_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanClayT4HypercubicRepresentativeSumExact as Representatives
import DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact as SourceSymmetry

cellVolume : ℚ
cellVolume = + 1 / 16

normalizedRegularSum : (Grid.GridCell4 → ℚ) → ℚ
normalizedRegularSum contribution =
  cellVolume * Sums.sumRational Grid.regularGridCells contribution

fourOrbitNormalizedValue : (Grid.GridCell4 → ℚ) → ℚ
fourOrbitNormalizedValue contribution =
  (+ 4 / 1) * contribution Orbit.oneOuterRepresentative
  + (+ 6 / 1) * contribution Orbit.twoOuterRepresentative
  + (+ 4 / 1) * contribution Orbit.threeOuterRepresentative
  + contribution Orbit.fourOuterRepresentative

sourceSymmetryNormalizedQuadrature :
  ∀ {contribution}
    (sourceSymmetry : SourceSymmetry.CMP109ScalarEuclideanSymmetry contribution) →
  normalizedRegularSum contribution ≡ fourOrbitNormalizedValue contribution
sourceSymmetryNormalizedQuadrature {contribution} sourceSymmetry =
  let
    invariant : Action.GeneratorInvariantRationalContribution contribution
    invariant = SourceSymmetry.asGeneratorInvariant sourceSymmetry

    rawReduction = Representatives.regularInvariantSumIsFourRepresentatives invariant
  in
  trans
    (cong (cellVolume *_) rawReduction)
    (ℚRing.solve-∀
      (contribution Orbit.oneOuterRepresentative)
      (contribution Orbit.twoOuterRepresentative)
      (contribution Orbit.threeOuterRepresentative)
      (contribution Orbit.fourOuterRepresentative))

cmp109SourceSymmetryFourOrbitQuadratureLevel : ProofLevel
cmp109SourceSymmetryFourOrbitQuadratureLevel = machineChecked

-- Physical L3 leaf: identify `contribution` with the literal Wilson/ghost/Haar
-- scalar expression produced from the background-field vacuum polarization,
-- and evaluate/enclose the four representative values in the Bishop carrier.
literalCMP109FourOrbitScalarContributionLevel : ProofLevel
literalCMP109FourOrbitScalarContributionLevel = conditional
