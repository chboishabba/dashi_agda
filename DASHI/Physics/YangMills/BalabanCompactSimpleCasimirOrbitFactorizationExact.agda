module DASHI.Physics.YangMills.BalabanCompactSimpleCasimirOrbitFactorizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Do not postpone compact-simple-group dependence to the final Clay
-- reconstruction theorem.  At one loop the physical group calculation must
-- still prove that its Wilson/ghost/Haar expression factors through the
-- adjoint quadratic Casimir.  ONCE that source-facing factorization is proved,
-- however, the finite four-orbit calculation should not be repeated for every
-- group.
--
-- This module proves the exact algebra needed for that separation:
--
--   C_A (S1 + S2 + S3 + S4)
--     = C_A S1 + C_A S2 + C_A S3 + C_A S4,
--
-- and transports any certified lower bound on the universal four-orbit scalar
-- through every nonnegative adjoint-Casimir scale.  Thus the numerical Bishop
-- enclosure can target one universal scalar; group-specific work is isolated
-- to proving the literal Casimir factorization and strict C_A > 0 for the
-- chosen compact simple group.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record FourOrbitScalar : Set where
  constructor fourOrbitScalar
  field
    oneOuter twoOuter threeOuter fourOuter : ℚ
open FourOrbitScalar public

fourOrbitTotal : FourOrbitScalar → ℚ
fourOrbitTotal orbit =
  oneOuter orbit + twoOuter orbit + threeOuter orbit + fourOuter orbit

scaleFourOrbit : ℚ → FourOrbitScalar → FourOrbitScalar
scaleFourOrbit scale orbit = fourOrbitScalar
  (scale * oneOuter orbit)
  (scale * twoOuter orbit)
  (scale * threeOuter orbit)
  (scale * fourOuter orbit)

casimirScaleCommutesWithFourOrbitTotal :
  ∀ scale orbit →
  fourOrbitTotal (scaleFourOrbit scale orbit)
  ≡ scale * fourOrbitTotal orbit
casimirScaleCommutesWithFourOrbitTotal scale orbit =
  ℚRing.solve-∀ scale
    (oneOuter orbit) (twoOuter orbit) (threeOuter orbit) (fourOuter orbit)

record CompactSimpleCasimirCarrier (GaugeGroup : Set) : Set₁ where
  field
    adjointCasimir : GaugeGroup → ℚ
    adjointCasimirNonnegative : ∀ group → 0ℚ ≤ adjointCasimir group
open CompactSimpleCasimirCarrier public

groupScaledOneLoopCoefficient :
  ∀ {GaugeGroup} → CompactSimpleCasimirCarrier GaugeGroup →
  GaugeGroup → FourOrbitScalar → ℚ
groupScaledOneLoopCoefficient carrier group orbit =
  adjointCasimir carrier group * fourOrbitTotal orbit

groupScaledOrbitTotalExact :
  ∀ {GaugeGroup}
    (carrier : CompactSimpleCasimirCarrier GaugeGroup)
    group orbit →
  fourOrbitTotal (scaleFourOrbit (adjointCasimir carrier group) orbit)
  ≡ groupScaledOneLoopCoefficient carrier group orbit
groupScaledOrbitTotalExact carrier group orbit =
  casimirScaleCommutesWithFourOrbitTotal (adjointCasimir carrier group) orbit

record UniversalFourOrbitLowerBound (orbit : FourOrbitScalar) : Set where
  field
    lower : ℚ
    lowerSound : lower ≤ fourOrbitTotal orbit
open UniversalFourOrbitLowerBound public

casimirTransportsUniversalLowerBound :
  ∀ {GaugeGroup}
    (carrier : CompactSimpleCasimirCarrier GaugeGroup)
    group orbit
    (bound : UniversalFourOrbitLowerBound orbit) →
  adjointCasimir carrier group * lower bound
  ≤ groupScaledOneLoopCoefficient carrier group orbit
casimirTransportsUniversalLowerBound carrier group orbit bound =
  Norm.scaleNonnegative
    (adjointCasimir carrier group)
    (adjointCasimirNonnegative carrier group)
    (lowerSound bound)

compactSimpleCasimirOrbitFactorizationLevel : ProofLevel
compactSimpleCasimirOrbitFactorizationLevel = machineChecked

compactSimpleCasimirLowerBoundTransportLevel : ProofLevel
compactSimpleCasimirLowerBoundTransportLevel = machineChecked

-- Remaining physical/group producer: derive the literal Wilson + Faddeev--Popov
-- ghost + Haar one-loop expression for a compact simple group and prove that
-- its colour contraction is exactly C_A times the universal scalar consumed
-- above.  Strict positivity C_A > 0 is also required when positivity rather
-- than a nonnegative lower-bound transport is the target.
literalWilsonGhostHaarCasimirFactorizationLevel : ProofLevel
literalWilsonGhostHaarCasimirFactorizationLevel = conditional
