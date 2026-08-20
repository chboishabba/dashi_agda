module DASHI.Physics.YangMills.BalabanClayT4HypercubicRepresentativeSumExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I.", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
-- Given invariance under the seven concrete signed-permutation generators, the
-- exact 240-cell regular sum collapses to FOUR representative values with
-- multiplicities 64,96,64,16.  This theorem uses the generated action and the
-- generated regular-cell list; no per-box equality receipt is accepted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _*_ ; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action

orbitValue :
  (Grid.GridCell4 → ℚ) → Orbit.OrbitClass → ℚ
orbitValue contribution Orbit.infrared =
  contribution (Action.representative Orbit.infrared)
orbitValue contribution Orbit.oneOuter =
  contribution Orbit.oneOuterRepresentative
orbitValue contribution Orbit.twoOuter =
  contribution Orbit.twoOuterRepresentative
orbitValue contribution Orbit.threeOuter =
  contribution Orbit.threeOuterRepresentative
orbitValue contribution Orbit.fourOuter =
  contribution Orbit.fourOuterRepresentative

canonicalizedContribution :
  (Grid.GridCell4 → ℚ) → Grid.GridCell4 → ℚ
canonicalizedContribution contribution cell =
  orbitValue contribution (Orbit.orbitClass cell)

invariantContributionCanonicalizes :
  ∀ {contribution}
    (invariant : Action.GeneratorInvariantRationalContribution contribution)
    cell →
  contribution cell ≡ canonicalizedContribution contribution cell
invariantContributionCanonicalizes invariant cell =
  Action.cellContributionEqualsOrbitRepresentative invariant cell

regularSumCanonicalizes :
  ∀ {contribution}
    (invariant : Action.GeneratorInvariantRationalContribution contribution) →
  Sums.sumRational Grid.regularGridCells contribution
  ≡ Sums.sumRational Grid.regularGridCells
      (canonicalizedContribution contribution)
regularSumCanonicalizes {contribution} invariant =
  Sums.sumRationalCong
    Grid.regularGridCells
    contribution
    (canonicalizedContribution contribution)
    (invariantContributionCanonicalizes invariant)

-- The right-hand side contains only four variables after reduction of the
-- generated finite grid.  Ring normalization then exposes the exact orbit
-- multiplicities.
canonicalizedRegularSumMultiplicity :
  ∀ contribution →
  Sums.sumRational Grid.regularGridCells
      (canonicalizedContribution contribution)
  ≡ (+ 64 / 1) * orbitValue contribution Orbit.oneOuter
    + (+ 96 / 1) * orbitValue contribution Orbit.twoOuter
    + (+ 64 / 1) * orbitValue contribution Orbit.threeOuter
    + (+ 16 / 1) * orbitValue contribution Orbit.fourOuter
canonicalizedRegularSumMultiplicity contribution =
  ℚRing.solve-∀
    (orbitValue contribution Orbit.oneOuter)
    (orbitValue contribution Orbit.twoOuter)
    (orbitValue contribution Orbit.threeOuter)
    (orbitValue contribution Orbit.fourOuter)

regularInvariantSumIsFourRepresentatives :
  ∀ {contribution}
    (invariant : Action.GeneratorInvariantRationalContribution contribution) →
  Sums.sumRational Grid.regularGridCells contribution
  ≡ (+ 64 / 1) * contribution Orbit.oneOuterRepresentative
    + (+ 96 / 1) * contribution Orbit.twoOuterRepresentative
    + (+ 64 / 1) * contribution Orbit.threeOuterRepresentative
    + (+ 16 / 1) * contribution Orbit.fourOuterRepresentative
regularInvariantSumIsFourRepresentatives {contribution} invariant =
  trans
    (regularSumCanonicalizes invariant)
    (canonicalizedRegularSumMultiplicity contribution)

hypercubicInvariantRegularSumReductionLevel : ProofLevel
hypercubicInvariantRegularSumReductionLevel = machineChecked

-- Physical leaf only: instantiate `GeneratorInvariantRationalContribution` for
-- the actual scalar Wilson/ghost/Haar orbit expression after Bishop interval
-- semantics has produced its rational certified contribution.
literalOneLoopFourRepresentativeReductionLevel : ProofLevel
literalOneLoopFourRepresentativeReductionLevel = conditional
