{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanModeIndexedPositiveGapCoreRound306Exact where

------------------------------------------------------------------------
-- ROUND306 / MINIMAL SPECTRAL-GAP CONSUMER AFTER DIRECT MODE EXCLUSION
--
-- The historical `ReconstructedClusteringSpectrum` record contains the lower
-- envelope, clustering envelope, mode observable and slow/fast contradiction.
-- R299-R305 now construct/use those only as producer machinery.  The actual gap
-- content is smaller:
--
--   * the selected candidate energy is positive;
--   * no positive spectral mode lies strictly below it.
--
-- Keep that terminal statement independent of the producer presentation.  This
-- is the shortest object that later needs a SAME-HAMILTONIAN weld to the Clay
-- physical Hamiltonian spectrum.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact as Rate302
import DASHI.Physics.YangMills.BalabanDirectT5PositiveSubgapExclusionRound305Exact as R305
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record ModeIndexedPositiveGapCore (Energy : Set) : Set₁ where
  field
    candidateEnergy : Energy
    PositiveEnergy : Energy → Set
    StrictlyBelow : Energy → Energy → Set
    SubgapMode : Energy → Set
    candidatePositive : PositiveEnergy candidateEnergy
    noPositiveSubgapMode : ∀ energy →
      PositiveEnergy energy → StrictlyBelow energy candidateEnergy →
      SubgapMode energy → Gap.Empty

open ModeIndexedPositiveGapCore public

compileDirectT5PositiveGapCore :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    {coordinate : Rate302.TransferEnergyDecayRatioCoordinate Energy} →
  R305.DirectT5PositiveSubgapExclusionPayment decomposition coordinate →
  ModeIndexedPositiveGapCore Energy
compileDirectT5PositiveGapCore {family = family} {coordinate = coordinate} payment = record
  { ModeIndexedPositiveGapCore.candidateEnergy = Rate302.candidateEnergy coordinate
  ; ModeIndexedPositiveGapCore.PositiveEnergy = Rate302.PositiveEnergy coordinate
  ; ModeIndexedPositiveGapCore.StrictlyBelow = Rate302.StrictlyBelow coordinate
  ; ModeIndexedPositiveGapCore.SubgapMode = R297.SubgapMode family
  ; ModeIndexedPositiveGapCore.candidatePositive = Rate302.candidateEnergyPositive coordinate
  ; ModeIndexedPositiveGapCore.noPositiveSubgapMode = R305.noPositiveSubgapMode payment
  }

record Round306Boundary : Set where
  constructor round306-boundary
  field
    historicalEnvelopeRecordPartOfGapContent : Bool
    historicalEnvelopeRecordPartOfGapContentIsFalse :
      historicalEnvelopeRecordPartOfGapContent ≡ false
    positiveCandidateAndNoSubgapSufficeForGapCore : Bool
    positiveCandidateAndNoSubgapSufficeForGapCoreIsTrue :
      positiveCandidateAndNoSubgapSufficeForGapCore ≡ true
    modeIndexedPositiveGapAfterPaymentsCompilerOwned : Bool
    modeIndexedPositiveGapAfterPaymentsCompilerOwnedIsTrue :
      modeIndexedPositiveGapAfterPaymentsCompilerOwned ≡ true

canonicalRound306Boundary : Round306Boundary
canonicalRound306Boundary = round306-boundary false refl true refl true refl

round306ModeIndexedPositiveGapCompilerLevel : ProofLevel
round306ModeIndexedPositiveGapCompilerLevel = machineChecked

round306PhysicalHamiltonianSpectrumSameObjectLevel : ProofLevel
round306PhysicalHamiltonianSpectrumSameObjectLevel = conditional
