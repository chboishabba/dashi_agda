{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDirectT5PositiveSubgapExclusionRound305Exact where

------------------------------------------------------------------------
-- ROUND305 / DIRECT T5 B1 + TRANSFER-RATE SPECTRAL SLICE
--
-- R303 still accepts `ContinuumSelectedCorrelationUpper` as an input.  R304
-- constructs that exact object from the finite T5 rooted shell, selected
-- support-distance=time, covariance convergence, and closed rational order.
-- Compose them here so the continuum clustering upper is no longer a primitive
-- spectral payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact as Rate302
import DASHI.Physics.YangMills.BalabanDirectPositiveSubgapExclusionRound303Exact as R303
import DASHI.Physics.YangMills.BalabanModeSelectedDirectT5ContinuumUpperRound304Exact as R304
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact as Geometry
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record DirectT5PositiveSubgapExclusionPayment
    {Measure TestObservable Energy Vector : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Data.Rational.Base.ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    (decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family)
    (coordinate : Rate302.TransferEnergyDecayRatioCoordinate Energy) : Set₁ where
  field
    modeRatioWeld : Rate302.ModeRatioUsesTransferCoordinate decomposition coordinate
    directUpperPayment : R304.ModeSelectedDirectT5UpperPayment
      dataSet extension tests quantitative family decomposition
    geometricDominance : Geometry.RationalGeometricDominance

open DirectT5PositiveSubgapExclusionPayment public

asRound303Payment :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Data.Rational.Base.ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    {coordinate : Rate302.TransferEnergyDecayRatioCoordinate Energy} →
  DirectT5PositiveSubgapExclusionPayment decomposition coordinate →
  R303.DirectPositiveSubgapExclusionPayment decomposition coordinate
asRound303Payment payment = record
  { R303.DirectPositiveSubgapExclusionPayment.modeRatioWeld = modeRatioWeld payment
  ; R303.DirectPositiveSubgapExclusionPayment.continuumUpper =
      R304.continuumSelectedUpper (directUpperPayment payment)
  ; R303.DirectPositiveSubgapExclusionPayment.geometricDominance =
      geometricDominance payment
  }

noPositiveSubgapMode :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Data.Rational.Base.ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    {coordinate : Rate302.TransferEnergyDecayRatioCoordinate Energy} →
  DirectT5PositiveSubgapExclusionPayment decomposition coordinate →
  ∀ energy (mode : R297.SubgapMode family energy) →
  Rate302.PositiveEnergy coordinate energy →
  Rate302.StrictlyBelow coordinate energy (Rate302.candidateEnergy coordinate) →
  Gap.Empty
noPositiveSubgapMode payment =
  R303.noPositiveSubgapMode (asRound303Payment payment)

record Round305Boundary : Set where
  constructor round305-boundary
  field
    continuumUpperIndependentPhysicalLeaf : Bool
    continuumUpperIndependentPhysicalLeafIsFalse :
      continuumUpperIndependentPhysicalLeaf ≡ false
    fullSpectrumRequiredToPropagateB1Upper : Bool
    fullSpectrumRequiredToPropagateB1UpperIsFalse :
      fullSpectrumRequiredToPropagateB1Upper ≡ false
    directT5ToPositiveSubgapExclusionCompilerOwned : Bool
    directT5ToPositiveSubgapExclusionCompilerOwnedIsTrue :
      directT5ToPositiveSubgapExclusionCompilerOwned ≡ true

canonicalRound305Boundary : Round305Boundary
canonicalRound305Boundary = round305-boundary false refl false refl true refl

round305DirectT5SubgapExclusionCompilerLevel : ProofLevel
round305DirectT5SubgapExclusionCompilerLevel = machineChecked

round305LiteralFiniteTwoJSourceShellLevel : ProofLevel
round305LiteralFiniteTwoJSourceShellLevel = R304.round304DirectFiniteTwoJSourceShellLevel

round305SameHamiltonianSpectralDecompositionLevel : ProofLevel
round305SameHamiltonianSpectralDecompositionLevel = R303.round303SpectralDecompositionLevel

round305PhysicalTransferEnergyDecayCoordinateLevel : ProofLevel
round305PhysicalTransferEnergyDecayCoordinateLevel =
  R303.round303TransferEnergyDecayCoordinateLevel
