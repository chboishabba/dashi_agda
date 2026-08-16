module DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions",
-- Communications in Mathematical Physics.
-- DOI: 10.1007/BF01239022.
--
-- Roman Kotecky and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- P. K. Mitter,
-- "The Exact Renormalization Group",
-- arXiv:math-ph/0505008.
--
-- DASHI CONTRIBUTION
--
-- Put the post-Gate-I campaign into one coupled invariant-region theorem
-- surface instead of six independent certificates whose constants can drift
-- apart.  The state carries, at minimum, a running coupling coordinate, a
-- small-field/polymer norm, a genuine large-field activity, a conditional
-- covariance norm, a lattice-unit exponential-decay exponent, and the inverse
-- physical lattice spacing needed to interpret that exponent.
--
-- The basic admissible region couples all four analytic budgets.  A stronger
-- physical-gap region additionally requires a uniform positive lower bound on
--
--   m_phys = mu_lattice * inverseSpacing.
--
-- This module also proves a concrete no-go regression: a unit lattice-decay
-- exponent can coexist with exactly zero physical mass when the physical-unit
-- conversion factor is zero.  Therefore a one-scale covariance contraction
-- can never be promoted to the Clay mass-gap endpoint without an explicit
-- physical-unit bridge and a uniform positive physical lower bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

record YM4RGState : Set where
  constructor rgState
  field
    runningCoupling : ℚ
    smallFieldPolymerNorm : ℚ
    largeFieldActivity : ℚ
    conditionalCovarianceNorm : ℚ
    latticeDecayExponent : ℚ
    inversePhysicalSpacing : ℚ

open YM4RGState public

physicalDecayMass : YM4RGState → ℚ
physicalDecayMass state =
  latticeDecayExponent state * inversePhysicalSpacing state

record YM4RGRegionParameters : Set where
  constructor regionParameters
  field
    couplingCap : ℚ
    smallFieldCap : ℚ
    largeFieldCap : ℚ
    covarianceCap : ℚ

open YM4RGRegionParameters public

record InYM4RGInvariantRegion
    (parameters : YM4RGRegionParameters)
    (state : YM4RGState) : Set where
  field
    couplingControlled : runningCoupling state ≤ couplingCap parameters
    smallFieldControlled :
      smallFieldPolymerNorm state ≤ smallFieldCap parameters
    largeFieldControlled :
      largeFieldActivity state ≤ largeFieldCap parameters
    covarianceControlled :
      conditionalCovarianceNorm state ≤ covarianceCap parameters
    latticeDecayNonnegative : 0ℚ ≤ latticeDecayExponent state
    inverseSpacingNonnegative : 0ℚ ≤ inversePhysicalSpacing state

open InYM4RGInvariantRegion public

record YM4RGOneStep
    (parameters : YM4RGRegionParameters) : Set₁ where
  field
    step : YM4RGState → YM4RGState
    preservesRegion : ∀ state →
      InYM4RGInvariantRegion parameters state →
      InYM4RGInvariantRegion parameters (step state)

open YM4RGOneStep public

iterateTwoStepsPreservesRegion :
  ∀ {parameters}
    (firstStep secondStep : YM4RGOneStep parameters)
    state →
  InYM4RGInvariantRegion parameters state →
  InYM4RGInvariantRegion parameters
    (step secondStep (step firstStep state))
iterateTwoStepsPreservesRegion firstStep secondStep state admissible =
  preservesRegion secondStep (step firstStep state)
    (preservesRegion firstStep state admissible)

------------------------------------------------------------------------
-- Physical-gap strengthening.
------------------------------------------------------------------------

record InYM4RGPhysicalGapRegion
    (parameters : YM4RGRegionParameters)
    (massFloor : ℚ)
    (state : YM4RGState) : Set where
  field
    analyticRegion : InYM4RGInvariantRegion parameters state
    massFloorPositive : 0ℚ < massFloor
    physicalMassAboveFloor : massFloor ≤ physicalDecayMass state

open InYM4RGPhysicalGapRegion public

record YM4RGPhysicalGapOneStep
    (parameters : YM4RGRegionParameters)
    (massFloor : ℚ) : Set₁ where
  field
    step : YM4RGState → YM4RGState
    preservesPhysicalGapRegion : ∀ state →
      InYM4RGPhysicalGapRegion parameters massFloor state →
      InYM4RGPhysicalGapRegion parameters massFloor (step state)

open YM4RGPhysicalGapOneStep public

physicalGapTwoStepPreservation :
  ∀ {parameters massFloor}
    (firstStep secondStep : YM4RGPhysicalGapOneStep parameters massFloor)
    state →
  InYM4RGPhysicalGapRegion parameters massFloor state →
  InYM4RGPhysicalGapRegion parameters massFloor
    (YM4RGPhysicalGapOneStep.step secondStep
      (YM4RGPhysicalGapOneStep.step firstStep state))
physicalGapTwoStepPreservation firstStep secondStep state admissible =
  preservesPhysicalGapRegion secondStep
    (YM4RGPhysicalGapOneStep.step firstStep state)
    (preservesPhysicalGapRegion firstStep state admissible)

------------------------------------------------------------------------
-- Concrete regression: lattice-unit decay is not a physical mass gap.
------------------------------------------------------------------------

latticeDecayOnlyCounterexample : YM4RGState
latticeDecayOnlyCounterexample =
  rgState 0ℚ 0ℚ 0ℚ 0ℚ 1ℚ 0ℚ

latticeDecayOnlyCounterexampleHasUnitLatticeExponent :
  latticeDecayExponent latticeDecayOnlyCounterexample ≡ 1ℚ
latticeDecayOnlyCounterexampleHasUnitLatticeExponent = refl

latticeDecayOnlyCounterexamplePhysicalMassZero :
  physicalDecayMass latticeDecayOnlyCounterexample ≡ 0ℚ
latticeDecayOnlyCounterexamplePhysicalMassZero = refl

ym4RGInvariantRegionLevel : ProofLevel
ym4RGInvariantRegionLevel = machineChecked

ym4RGPhysicalGapRegionLevel : ProofLevel
ym4RGPhysicalGapRegionLevel = machineChecked

ym4LatticeDecayDoesNotAloneProvePhysicalGapLevel : ProofLevel
ym4LatticeDecayDoesNotAloneProvePhysicalGapLevel = machineChecked
