module DASHI.Physics.Closure.R2P2OpticalLattice369HamiltonianCutExact where

------------------------------------------------------------------------
-- OPTICAL LATTICE / 369 CONTROL MAX-CUT (source-written finite adapter).
--
-- Prior science:
--   Aubry & Andre (1980), localization for the incommensurate chain.
--   Bothwell, Ye et al. (Nature 2022), vertical Sr clock redshift.
--   Ma, Stoeltzel, Christensen et al. (arXiv:2610.17499v2,
--   2026-10-14), horizontal 87Sr bichromatic 813/497-nm lattice.
--   Triano et al. (APS DAMOP 2026), R2P2 neutral-Yb mountain clocks.
--
-- These are three DIFFERENT experimental referents.
--
-- The AA Hamiltonian is H = -J(T+T†) + Δ cos(2π β i+φ),
-- with irrational/experimentally incommensurate β and calibrated J, Δ.
-- We do NOT import that continuum/infinite-chain theorem.
-- This minimal three-site mathematical cut retains only an unsigned
-- nearest-neighbour adjacency operator and a distinct site-potential
-- operator. Their commutator is nonzero on a concrete basis state.
-- Finite 3-site adjacency ≠ quasi-periodic AA localization/threshold,
-- Bloch bands, magic wavelength, Ramsey contrast or clock error budget.
--
-- Prior DASHI owners remain unchanged. The finite operator names,
-- source-typed experimental split and specific commutator example
-- are the new constructions in this adapter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atom
import DASHI.Physics.Closure.WolfPrize2026UltracoldControlBridge as Wolf
import DASHI.Physics.Closure.BothwellYe2022MillimetreRedshiftReceipt as Ye
import DASHI.Physics.Closure.R2P2MountainOpticalClockComparisonExact as R2P2
import DASHI.Physics.Closure.R2P2369WaveOpticalCombInformationCutExact as WaveCut

-- Three sites constitute a tiny finite test graph, NOT a physical 3/6/9 law.
data ThreeSiteVector : Set where
  threeSiteVector : Nat → Nat → Nat → ThreeSiteVector

-- Unsigned adjacency skeleton of a three-site *path* P3.
-- Physical -J amplitude, optical phase and normalisation NOT selected.
nearestNeighbourAdjacency : ThreeSiteVector → ThreeSiteVector
nearestNeighbourAdjacency (threeSiteVector left middle right) =
  threeSiteVector middle (left + right) middle

-- Finite site-dependent, unsigned toy potential weights 0,1,2.
-- This is NOT cos(2π β i + φ) or a fitted AA secondary lattice.
siteDependentPotential : ThreeSiteVector → ThreeSiteVector
siteDependentPotential (threeSiteVector left middle right) =
  threeSiteVector 0 middle (2 * right)

leftBasisState : ThreeSiteVector
leftBasisState = threeSiteVector 1 0 0

middleBasisState : ThreeSiteVector
middleBasisState = threeSiteVector 0 1 0

zeroSiteState : ThreeSiteVector
zeroSiteState = threeSiteVector 0 0 0

adjacencyLeftGoesMiddle :
  nearestNeighbourAdjacency leftBasisState ≡ middleBasisState
adjacencyLeftGoesMiddle = refl

potentialAnnihilatesLeft :
  siteDependentPotential leftBasisState ≡ zeroSiteState
potentialAnnihilatesLeft = refl

potentialAfterHoppingMovesSiteWeight :
  siteDependentPotential (nearestNeighbourAdjacency leftBasisState)
  ≡ middleBasisState
potentialAfterHoppingMovesSiteWeight = refl

hoppingAfterPotentialIsZero :
  nearestNeighbourAdjacency (siteDependentPotential leftBasisState)
  ≡ zeroSiteState
hoppingAfterPotentialIsZero = refl

-- The two concrete operators DO NOT commute on this three-site witness.
-- This is a genuine finite nontrivial counterexample, not a physical
-- simulation or an AA localization transition.
finiteLatticeOperatorsFailToCommute :
  nearestNeighbourAdjacency (siteDependentPotential leftBasisState)
  ≡ siteDependentPotential (nearestNeighbourAdjacency leftBasisState)
  → ⊥
finiteLatticeOperatorsFailToCommute ()

-- The 87Sr atomic identity is taken from the EXISTING periodic-table owner.
-- Proton number 38 and mass number 87 imply neutron number 49.
strontium87Index : Atom.AtomicIndex
strontium87Index = Atom.neutralAt 38 49

strontium87Neutral : Atom.Neutral strontium87Index
strontium87Neutral = Atom.neutralAtIsNeutral 38 49

-- The 171Yb identity is a *model label* and not independently established
-- for each R2P2 clock by the June APS abstract (it specifies neutral Yb).
ytterbium171ExampleOnly : Atom.AtomicIndex
ytterbium171ExampleOnly = Atom.neutralAt 70 101

data ClockExperimentLane : Set where
  maBichromaticSr87 : ClockExperimentLane
  bothwellYeVerticalSr : ClockExperimentLane
  trianaMountainYb : ClockExperimentLane

maIsNotTheR2P2Clock :
  maBichromaticSr87 ≡ trianaMountainYb → ⊥
maIsNotTheR2P2Clock ()

yeIsNotTheMaClock :
  bothwellYeVerticalSr ≡ maBichromaticSr87 → ⊥
yeIsNotTheMaClock ()

yeIsNotTheR2P2Clock :
  bothwellYeVerticalSr ≡ trianaMountainYb → ⊥
yeIsNotTheR2P2Clock ()

record OpticalLattice369PhysicalAuthority : Set where
  field
    wolfBridge : Wolf.WolfPrize2026UltracoldControlBridge
    wolfBridgeCanonical :
      wolfBridge ≡ Wolf.canonicalWolfPrize2026UltracoldControlBridge
    yeVerticalSrRedshift : Ye.BothwellYe2022ReceiptBoundary
    yeVerticalSrRedshiftCanonical :
      yeVerticalSrRedshift ≡ Ye.canonicalBothwellYe2022ReceiptBoundary
    mountainYbSource : R2P2.R2P2ClockComparisonBoundary
    mountainYbSourceCanonical :
      mountainYbSource ≡ R2P2.canonicalR2P2ClockComparisonBoundary
    signedOpticalCombWave : WaveCut.WaveCombAuthorityBoundary
    signedOpticalCombWaveCanonical :
      signedOpticalCombWave ≡ WaveCut.canonicalWaveCombAuthorityBoundary
    maStudySource : String
    maStudyReferenceClock : ClockExperimentLane
    maStudyReferenceClockIsSr87 :
      maStudyReferenceClock ≡ maBichromaticSr87
    finiteHoppingPotentialNoncommutativity :
      nearestNeighbourAdjacency (siteDependentPotential leftBasisState)
      ≡ siteDependentPotential (nearestNeighbourAdjacency leftBasisState)
      → ⊥
    maMagicLatticeTransferToR2P2Verified : Bool
    maMagicLatticeTransferToR2P2VerifiedIsFalse :
      maMagicLatticeTransferToR2P2Verified ≡ false
    finiteP3ProvesInfiniteAAThreshold : Bool
    finiteP3ProvesInfiniteAAThresholdIsFalse :
      finiteP3ProvesInfiniteAAThreshold ≡ false
    opticalLatticeControlsMetricRedshift : Bool
    opticalLatticeControlsMetricRedshiftIsFalse :
      opticalLatticeControlsMetricRedshift ≡ false
    actualR2P2TrapDepthMeasuredHere : Bool
    actualR2P2TrapDepthMeasuredHereIsFalse :
      actualR2P2TrapDepthMeasuredHere ≡ false
    maPublishedCoherenceDataIngested : Bool
    maPublishedCoherenceDataIngestedIsFalse :
      maPublishedCoherenceDataIngested ≡ false
    measuredQuantumGravityObserved : Bool
    measuredQuantumGravityObservedIsFalse :
      measuredQuantumGravityObserved ≡ false
    nextNecessaryEvidence : List String

open OpticalLattice369PhysicalAuthority public

canonicalOpticalLattice369PhysicalAuthority :
  OpticalLattice369PhysicalAuthority
canonicalOpticalLattice369PhysicalAuthority = record
  { wolfBridge = Wolf.canonicalWolfPrize2026UltracoldControlBridge
  ; wolfBridgeCanonical = refl
  ; yeVerticalSrRedshift = Ye.canonicalBothwellYe2022ReceiptBoundary
  ; yeVerticalSrRedshiftCanonical = refl
  ; mountainYbSource = R2P2.canonicalR2P2ClockComparisonBoundary
  ; mountainYbSourceCanonical = refl
  ; signedOpticalCombWave = WaveCut.canonicalWaveCombAuthorityBoundary
  ; signedOpticalCombWaveCanonical = refl
  ; maStudySource =
      "Ma, Stoeltzel, Christensen et al., arXiv:2610.17499v2, 2026-10-14; 87Sr 813/497 nm horizontal bichromatic lattice clock"
  ; maStudyReferenceClock = maBichromaticSr87
  ; maStudyReferenceClockIsSr87 = refl
  ; finiteHoppingPotentialNoncommutativity =
      finiteLatticeOperatorsFailToCommute
  ; maMagicLatticeTransferToR2P2Verified = false
  ; maMagicLatticeTransferToR2P2VerifiedIsFalse = refl
  ; finiteP3ProvesInfiniteAAThreshold = false
  ; finiteP3ProvesInfiniteAAThresholdIsFalse = refl
  ; opticalLatticeControlsMetricRedshift = false
  ; opticalLatticeControlsMetricRedshiftIsFalse = refl
  ; actualR2P2TrapDepthMeasuredHere = false
  ; actualR2P2TrapDepthMeasuredHereIsFalse = refl
  ; maPublishedCoherenceDataIngested = false
  ; maPublishedCoherenceDataIngestedIsFalse = refl
  ; measuredQuantumGravityObserved = false
  ; measuredQuantumGravityObservedIsFalse = refl
  ; nextNecessaryEvidence =
      "calibrated primary/secondary optical lattice wavelengths and depth"
      ∷ "87Sr Ma paper source data versus 171Yb model versus R2P2 neutral Yb apparatus"
      ∷ "atomic polarizabilities, magic-frequency differential Stark shift and blackbody uncertainty"
      ∷ "tight-binding J and Δ calibration and irrational-beta finite-size error"
      ∷ "Rabi linewidth, Ramsey contrast and time-series uncertainty"
      ∷ "independent R2P2 optical transfer and geodetic ratio evidence"
      ∷ []
  }

latticeCannotProveInfiniteAAThreshold :
  finiteP3ProvesInfiniteAAThreshold
    canonicalOpticalLattice369PhysicalAuthority ≡ false
latticeCannotProveInfiniteAAThreshold =
  finiteP3ProvesInfiniteAAThresholdIsFalse
    canonicalOpticalLattice369PhysicalAuthority

latticeDoesNotConflateClockExperiments :
  maMagicLatticeTransferToR2P2Verified
    canonicalOpticalLattice369PhysicalAuthority ≡ false
latticeDoesNotConflateClockExperiments =
  maMagicLatticeTransferToR2P2VerifiedIsFalse
    canonicalOpticalLattice369PhysicalAuthority

latticeDoesNotObserveQuantumGravity :
  measuredQuantumGravityObserved
    canonicalOpticalLattice369PhysicalAuthority ≡ false
latticeDoesNotObserveQuantumGravity =
  measuredQuantumGravityObservedIsFalse
    canonicalOpticalLattice369PhysicalAuthority
