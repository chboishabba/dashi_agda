module DASHI.Physics.YangMills.BalabanCompactSimpleWilsonOneLoopOrbitAdapterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
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
-- DASHI CONTRIBUTION
--
-- Weld the exact Round57 four-orbit repartition to the Round58 compact-simple
-- Casimir factorization.  This proves that, after the PHYSICAL colour algebra
-- has identified a Wilson/ghost/Haar integrand as C_A times one universal
-- scalar contribution, the finite 240-cell calculation is literally reusable:
-- its four orbit sums are the universal object and C_A is applied only once.
--
-- No generic-group physics is assumed here.  The remaining physical theorem
-- is explicitly the source-facing colour contraction / Haar / ghost vertex
-- identity that establishes the C_A factorization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact as Orbit
import DASHI.Physics.YangMills.BalabanCompactSimpleCasimirOrbitFactorizationExact as Casimir

universalFourOrbitScalar :
  (Grid.GridCell4 → ℚ) → Casimir.FourOrbitScalar
universalFourOrbitScalar contribution = Casimir.fourOrbitScalar
  (Orbit.oneOuterOrbitSum contribution)
  (Orbit.twoOuterOrbitSum contribution)
  (Orbit.threeOuterOrbitSum contribution)
  (Orbit.fourOuterOrbitSum contribution)

universalFourOrbitTotalIsRegularCellSum :
  ∀ contribution →
  Casimir.fourOrbitTotal (universalFourOrbitScalar contribution)
  ≡ Sums.sumRational Grid.regularGridCells contribution
universalFourOrbitTotalIsRegularCellSum contribution =
  sym (Orbit.regularCellSumAsFourJointOrbitSums contribution)

casimirScaledRegularCellCoefficient :
  ∀ {GaugeGroup} → Casimir.CompactSimpleCasimirCarrier GaugeGroup →
  GaugeGroup → (Grid.GridCell4 → ℚ) → ℚ
casimirScaledRegularCellCoefficient carrier group contribution =
  Casimir.adjointCasimir carrier group
  * Sums.sumRational Grid.regularGridCells contribution

casimirScaledFourOrbitCoefficientIsRegularCellCoefficient :
  ∀ {GaugeGroup}
    (carrier : Casimir.CompactSimpleCasimirCarrier GaugeGroup)
    group contribution →
  Casimir.groupScaledOneLoopCoefficient carrier group
    (universalFourOrbitScalar contribution)
  ≡ casimirScaledRegularCellCoefficient carrier group contribution
casimirScaledFourOrbitCoefficientIsRegularCellCoefficient carrier group contribution =
  cong (Casimir.adjointCasimir carrier group *_)
    (universalFourOrbitTotalIsRegularCellSum contribution)

casimirScaledUniversalLowerBoundControlsRegularCellCoefficient :
  ∀ {GaugeGroup}
    (carrier : Casimir.CompactSimpleCasimirCarrier GaugeGroup)
    group contribution
    (bound : Casimir.UniversalFourOrbitLowerBound
      (universalFourOrbitScalar contribution)) →
  Casimir.adjointCasimir carrier group * Casimir.lower bound
  ≤ casimirScaledRegularCellCoefficient carrier group contribution
casimirScaledUniversalLowerBoundControlsRegularCellCoefficient
    carrier group contribution bound =
  let
    scaledLower =
      Casimir.casimirTransportsUniversalLowerBound
        carrier group (universalFourOrbitScalar contribution) bound
  in
  subst
    (λ coefficient →
      Casimir.adjointCasimir carrier group * Casimir.lower bound ≤ coefficient)
    (casimirScaledFourOrbitCoefficientIsRegularCellCoefficient
      carrier group contribution)
    scaledLower

compactSimpleWilsonOrbitAdapterLevel : ProofLevel
compactSimpleWilsonOrbitAdapterLevel = machineChecked

compactSimpleWilsonLowerBoundReuseLevel : ProofLevel
compactSimpleWilsonLowerBoundReuseLevel = machineChecked

literalCompactSimpleWilsonGhostHaarColourReductionLevel : ProofLevel
literalCompactSimpleWilsonGhostHaarColourReductionLevel = conditional
