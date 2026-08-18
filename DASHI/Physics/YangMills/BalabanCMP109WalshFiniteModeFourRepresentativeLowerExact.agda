module DASHI.Physics.YangMills.BalabanCMP109WalshFiniteModeFourRepresentativeLowerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.  Section 5, especially (5.6)--(5.8).
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213.
--
-- DASHI CONTRIBUTION
--
-- Cross-pollinate the exact CMP109 Walsh/orbit reduction with the finite-mode
-- one-loop lower-bound compiler.  Reflection covariance has already killed all
-- nontrivial sign characters, and permutation covariance gives
--
--   sum_regular I = 64 I_1 + 96 I_2 + 64 I_3 + 16 I_4.
--
-- Consequently a rigorous lower enclosure of the complete 240-cell regular
-- contribution requires only four representative lower bounds.  This module
-- proves the weighted monotonicity exactly over rationals; no 240 independent
-- interval receipts remain on the one-loop critical path once source symmetry
-- is established for the literal scalar integrand.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact as Source
import DASHI.Physics.YangMills.BalabanCMP109WalshFourOrbitFactorizationExact as FourOrbit

w1 w2 w3 w4 : ℚ
w1 = + 64 / 1
w2 = + 96 / 1
w3 = + 64 / 1
w4 = + 16 / 1

w1Nonnegative : 0ℚ ≤ w1
w1Nonnegative = ℚP.nonNegative⁻¹ w1
w2Nonnegative : 0ℚ ≤ w2
w2Nonnegative = ℚP.nonNegative⁻¹ w2
w3Nonnegative : 0ℚ ≤ w3
w3Nonnegative = ℚP.nonNegative⁻¹ w3
w4Nonnegative : 0ℚ ≤ w4
w4Nonnegative = ℚP.nonNegative⁻¹ w4

record FourRepresentativeLower
    (contribution : Grid.GridCell4 → ℚ) : Set where
  field
    lower1 lower2 lower3 lower4 : ℚ
    lower1Sound : lower1 ≤ contribution Orbit.oneOuterRepresentative
    lower2Sound : lower2 ≤ contribution Orbit.twoOuterRepresentative
    lower3Sound : lower3 ≤ contribution Orbit.threeOuterRepresentative
    lower4Sound : lower4 ≤ contribution Orbit.fourOuterRepresentative

open FourRepresentativeLower public

weightedRepresentativeLower :
  ∀ {contribution} → FourRepresentativeLower contribution → ℚ
weightedRepresentativeLower lower =
  w1 * lower1 lower
  + w2 * lower2 lower
  + w3 * lower3 lower
  + w4 * lower4 lower

weightedRepresentativeActual :
  (contribution : Grid.GridCell4 → ℚ) → ℚ
weightedRepresentativeActual contribution =
  w1 * contribution Orbit.oneOuterRepresentative
  + w2 * contribution Orbit.twoOuterRepresentative
  + w3 * contribution Orbit.threeOuterRepresentative
  + w4 * contribution Orbit.fourOuterRepresentative

weightedRepresentativeLowerSound :
  ∀ {contribution}
    (lower : FourRepresentativeLower contribution) →
  weightedRepresentativeLower lower
  ≤ weightedRepresentativeActual contribution
weightedRepresentativeLowerSound lower =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (Norm.scaleNonnegative w1 w1Nonnegative (lower1Sound lower))
        (Norm.scaleNonnegative w2 w2Nonnegative (lower2Sound lower)))
      (Norm.scaleNonnegative w3 w3Nonnegative (lower3Sound lower)))
    (Norm.scaleNonnegative w4 w4Nonnegative (lower4Sound lower))

regularGridLowerFromFourRepresentatives :
  ∀ {contribution : Grid.GridCell4 → ℚ}
    (symmetry : Source.CMP109ScalarEuclideanSymmetry contribution)
    (lower : FourRepresentativeLower contribution) →
  weightedRepresentativeLower lower
  ≤ Sums.sumRational Grid.regularGridCells contribution
regularGridLowerFromFourRepresentatives symmetry lower =
  subst
    (λ upper → weightedRepresentativeLower lower ≤ upper)
    (sym (FourOrbit.sourceSymmetryRegularSumIsFourTrivialRepresentatives symmetry))
    (weightedRepresentativeLowerSound lower)

cmp109FourRepresentativeLowerReductionLevel : ProofLevel
cmp109FourRepresentativeLowerReductionLevel = machineChecked

-- Physical input after this reduction: four representative interval lower
-- bounds for the literal Wilson/ghost/Haar scalar contribution.
literalFourRepresentativeBishopEnclosuresLevel : ProofLevel
literalFourRepresentativeBishopEnclosuresLevel = conditional
