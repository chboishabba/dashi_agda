{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSourceNativeTransferEnergyRatioRound400Exact where

------------------------------------------------------------------------
-- ROUND400 / SOURCE-NATIVE FAST RATIO ON THE EXISTING TRANSFER COORDINATE
--
-- R302 already isolates the genuine OS/transfer-semigroup content as ONE
-- order-reversing coordinate
--
--     energy <-> decay ratio.
--
-- Its candidate energy is specialized to ratio 1/2 only because the historical
-- clustering producer used the dyadic envelope.  R387 shows that the terminal
-- contradiction only needs the actual source-native fast ratio q_fast.
--
-- Therefore no fresh family of statements
--
--     q_fast < q_E < 1
--
-- is primitive.  Once the SAME reconstructed Hamiltonian uses R302's transfer
-- coordinate and the candidate energy is `energyOfRatio q_fast`, strict energy
-- ordering and positive energy compile those inequalities.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact as R302

sourceNativeCandidateEnergy :
  ∀ {Energy} → R302.TransferEnergyDecayRatioCoordinate Energy → ℚ → Energy
sourceNativeCandidateEnergy coordinate fastRatio =
  R302.energyOfRatio coordinate fastRatio

sourceNativeCandidateEnergyPositive :
  ∀ {Energy}
    (coordinate : R302.TransferEnergyDecayRatioCoordinate Energy)
    (fastRatio : ℚ) →
  0ℚ ≤ fastRatio → fastRatio < 1ℚ →
  R302.PositiveEnergy coordinate
    (sourceNativeCandidateEnergy coordinate fastRatio)
sourceNativeCandidateEnergyPositive coordinate fastRatio fastNN fastBelowOne =
  R302.strictRatioMapsToPositiveEnergy coordinate
    fastRatio fastNN fastBelowOne

sourceNativePositiveSubgapRatioBounds :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    {coordinate : R302.TransferEnergyDecayRatioCoordinate Energy}
    (weld : R302.ModeRatioUsesTransferCoordinate decomposition coordinate)
    (fastRatio : ℚ)
    energy (mode : R297.SubgapMode family energy) →
  R302.PositiveEnergy coordinate energy →
  R302.StrictlyBelow coordinate energy
    (sourceNativeCandidateEnergy coordinate fastRatio) →
  (fastRatio < R300.subgapRatio decomposition energy mode)
  × (R300.subgapRatio decomposition energy mode < 1ℚ)
sourceNativePositiveSubgapRatioBounds
    {decomposition = decomposition} {coordinate = coordinate}
    weld fastRatio energy mode positive below =
  let
    slowerRaw = R302.strictEnergyOrderReversesDecayRatio coordinate
      energy (sourceNativeCandidateEnergy coordinate fastRatio) below

    candidateRatio =
      R302.ratioOfEnergyOfRatio coordinate fastRatio

    modeRatio = R302.modeRatioIsEnergyRatio weld energy mode

    slower = ℚP.subst₂
      (λ left right → left < right)
      candidateRatio
      (sym modeRatio)
      slowerRaw

    belowOneRaw =
      R302.positiveEnergyHasStrictDecayRatio coordinate energy positive

    belowOne = subst
      (λ ratio → ratio < 1ℚ)
      (sym modeRatio)
      belowOneRaw
  in
  slower , belowOne

------------------------------------------------------------------------
-- The remaining physical same-Hamiltonian weld for the source-native route.
------------------------------------------------------------------------

record SourceNativeCandidateUsesTransferCoordinate
    {Energy : Set}
    (coordinate : R302.TransferEnergyDecayRatioCoordinate Energy)
    (fastRatio : ℚ) : Set₁ where
  field
    gapCandidate : Energy
    gapCandidateIsSourceRatioEnergy :
      gapCandidate ≡ sourceNativeCandidateEnergy coordinate fastRatio

open SourceNativeCandidateUsesTransferCoordinate public

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round400SourceNativeTransferCompilerLevel : ProofLevel
round400SourceNativeTransferCompilerLevel = machineChecked

separatePositiveSubgapRateFamilyRequired : Bool
separatePositiveSubgapRateFamilyRequired = false

separatePositiveSubgapRateFamilyRequiredIsFalse :
  separatePositiveSubgapRateFamilyRequired ≡ false
separatePositiveSubgapRateFamilyRequiredIsFalse = refl

oneOrderReversingTransferCoordinateReused : Bool
oneOrderReversingTransferCoordinateReused = true

oneOrderReversingTransferCoordinateReusedIsTrue :
  oneOrderReversingTransferCoordinateReused ≡ true
oneOrderReversingTransferCoordinateReusedIsTrue = refl

sourceRateCandidateIdentificationStillProofBearing : Bool
sourceRateCandidateIdentificationStillProofBearing = true

sourceRateCandidateIdentificationStillProofBearingIsTrue :
  sourceRateCandidateIdentificationStillProofBearing ≡ true
sourceRateCandidateIdentificationStillProofBearingIsTrue = refl

sameHamiltonianModeRatioWeldStillProofBearing : Bool
sameHamiltonianModeRatioWeldStillProofBearing = true

sameHamiltonianModeRatioWeldStillProofBearingIsTrue :
  sameHamiltonianModeRatioWeldStillProofBearing ≡ true
sameHamiltonianModeRatioWeldStillProofBearingIsTrue = refl

freshSpectralDominanceAnalysisRequired : Bool
freshSpectralDominanceAnalysisRequired = false

freshSpectralDominanceAnalysisRequiredIsFalse :
  freshSpectralDominanceAnalysisRequired ≡ false
freshSpectralDominanceAnalysisRequiredIsFalse = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
