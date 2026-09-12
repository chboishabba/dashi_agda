{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPairwiseMassRateFromTransferCoordinateRound311Exact where

------------------------------------------------------------------------
-- ROUND311 / G3 REUSES THE EXISTING TRANSFER-ENERGY <-> DECAY COORDINATE
--
-- R305 leaves one physical normalization seam: the concrete q = 1/2 pairwise
-- clustering bound must mean exponential decay at one positive mass on the SAME
-- reconstructed Hamiltonian.  R302 already owns exactly the reusable physical
-- coordinate needed for that interpretation: an order-reversing transfer-energy
-- <-> decay-ratio system, with candidateEnergy = energyOfRatio(1/2) and a proof
-- that every strict ratio in [0,1) maps to positive energy.
--
-- Do not create a second mass-rate convention.  This adapter chooses Mass =
-- Energy, chooses the R302 candidate energy as the R305 mass parameter, and
-- packages the q=1/2 inequality as the exact decay proposition consumed by the
-- normalized clustering->spectrum authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304
import DASHI.Physics.YangMills.BalabanPairwiseClusteringStandardMassGapRound305Exact as R305
import DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact as R302

record SameHamiltonianTransferCoordinate
    (Hamiltonian Energy : Set) : Set₁ where
  field
    reconstructedHamiltonian : Hamiltonian
    coordinate : R302.TransferEnergyDecayRatioCoordinate Energy

open SameHamiltonianTransferCoordinate public

record HalfRateDecayMeaning
    {Measure TestObservable PhysicalObservable Hamiltonian Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (pairwise : R304.PhysicalPairwiseTimePresentation dataSet extension finite)
    (transfer : SameHamiltonianTransferCoordinate Hamiltonian Energy)
    : Set₁ where
  field
    -- Semantic proposition used by the standard clustering->spectrum theorem.
    ExponentialDecayBound :
      PhysicalObservable → PhysicalObservable → Nat → ℚ → Energy → Set

    -- The concrete q=1/2 bound proved by R304 is exactly that proposition at
    -- the energy selected by the transfer coordinate.
    halfRateBoundMeaning : ∀ left right time →
      R304.continuumPairCorrelation pairwise left right time
        ≤ Shell.quarter * Power.rationalPower Geo.half time →
      ExponentialDecayBound left right time
        (R304.continuumPairCorrelation pairwise left right time)
        (R302.candidateEnergy (coordinate transfer))

open HalfRateDecayMeaning public

asPairwiseClusteringMassRatePresentation :
  ∀ {Measure TestObservable PhysicalObservable Hamiltonian Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {pairwise : R304.PhysicalPairwiseTimePresentation dataSet extension finite}
    (transfer : SameHamiltonianTransferCoordinate Hamiltonian Energy) →
  HalfRateDecayMeaning pairwise transfer →
  R305.PairwiseClusteringMassRatePresentation pairwise
asPairwiseClusteringMassRatePresentation transfer meaning = record
  { R305.PairwiseClusteringMassRatePresentation.reconstructedHamiltonian =
      reconstructedHamiltonian transfer
  ; R305.PairwiseClusteringMassRatePresentation.massParameter =
      R302.candidateEnergy (coordinate transfer)
  ; R305.PairwiseClusteringMassRatePresentation.PositiveMass =
      R302.PositiveEnergy (coordinate transfer)
  ; R305.PairwiseClusteringMassRatePresentation.massParameterPositive =
      R302.candidateEnergyPositive (coordinate transfer)
  ; R305.PairwiseClusteringMassRatePresentation.ExponentialDecayBound =
      ExponentialDecayBound meaning
  ; R305.PairwiseClusteringMassRatePresentation.quarterHalfBoundHasPhysicalMassMeaning =
      halfRateBoundMeaning meaning
  }

record Round311Boundary : Set where
  constructor round311-boundary
  field
    independentSecondMassRateCoordinateRequired : Bool
    independentSecondMassRateCoordinateRequiredIsFalse :
      independentSecondMassRateCoordinateRequired ≡ false

    existingTransferCoordinateReused : Bool
    existingTransferCoordinateReusedIsTrue :
      existingTransferCoordinateReused ≡ true

    candidateMassPositivityAfterTransferCoordinateCompilerOwned : Bool
    candidateMassPositivityAfterTransferCoordinateCompilerOwnedIsTrue :
      candidateMassPositivityAfterTransferCoordinateCompilerOwned ≡ true

    halfRatePhysicalDecayMeaningStillRequired : Bool
    halfRatePhysicalDecayMeaningStillRequiredIsTrue :
      halfRatePhysicalDecayMeaningStillRequired ≡ true

canonicalRound311Boundary : Round311Boundary
canonicalRound311Boundary =
  round311-boundary false refl true refl true refl true refl

round311PairwiseMassRateAdapterLevel : ProofLevel
round311PairwiseMassRateAdapterLevel = machineChecked

round311TransferEnergyDecayCoordinateLevel : ProofLevel
round311TransferEnergyDecayCoordinateLevel =
  R302.round302PhysicalTransferEnergyDecayCoordinateLevel

-- This is the remaining same-Hamiltonian semantic payment after reusing R302:
-- the exact q=1/2 correlation inequality must be the exponential-decay
-- proposition used by the standard spectral transfer on this reconstructed
-- Hamiltonian.
round311HalfRatePhysicalDecayMeaningLevel : ProofLevel
round311HalfRatePhysicalDecayMeaningLevel = conditional
