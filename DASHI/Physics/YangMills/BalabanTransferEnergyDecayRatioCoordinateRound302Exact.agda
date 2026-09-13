{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact where

------------------------------------------------------------------------
-- ROUND302 / ONE TRANSFER-ENERGY <-> DECAY-RATIO COORDINATE PAYS OLD F4+F5
--
-- R298 separates
--
--   F4: E < m* -> 1/2 < q_E < 1
--   F5: q=1/2 is the SAME reconstructed candidate energy m*.
--
-- On a positive transfer semigroup these are one order-reversing coordinate.
-- This owner factors that normalization once.  It deliberately does NOT compile
-- the older overstrong record that demanded q_E<1 for every mode without a
-- PositiveEnergy premise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanClusteringDecayRatioToGapRound285Exact as R285
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record TransferEnergyDecayRatioCoordinate (Energy : Set) : Set₁ where
  field
    PositiveEnergy : Energy → Set
    StrictlyBelow : Energy → Energy → Set

    ratioOfEnergy : Energy → ℚ
    energyOfRatio : ℚ → Energy

    ratioOfEnergyOfRatio : ∀ ratio →
      ratioOfEnergy (energyOfRatio ratio) ≡ ratio

    strictRatioMapsToPositiveEnergy : ∀ ratio →
      0ℚ ≤ ratio → ratio < 1ℚ →
      PositiveEnergy (energyOfRatio ratio)

    positiveEnergyHasStrictDecayRatio : ∀ energy →
      PositiveEnergy energy → ratioOfEnergy energy < 1ℚ

    strictEnergyOrderReversesDecayRatio : ∀ lower higher →
      StrictlyBelow lower higher →
      ratioOfEnergy higher < ratioOfEnergy lower

open TransferEnergyDecayRatioCoordinate public

candidateEnergy : ∀ {Energy} → TransferEnergyDecayRatioCoordinate Energy → Energy
candidateEnergy coordinate = energyOfRatio coordinate Geo.half

candidateEnergyPositive :
  ∀ {Energy} (coordinate : TransferEnergyDecayRatioCoordinate Energy) →
  PositiveEnergy coordinate (candidateEnergy coordinate)
candidateEnergyPositive coordinate =
  strictRatioMapsToPositiveEnergy coordinate Geo.half
    Geo.halfNonnegative R274.halfStrictlyBelowOne

record ModeRatioUsesTransferCoordinate
    {Measure TestObservable Energy Vector : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    (decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family)
    (coordinate : TransferEnergyDecayRatioCoordinate Energy) : Set₁ where
  field
    modeRatioIsEnergyRatio :
      ∀ energy (mode : R297.SubgapMode family energy) →
      R300.subgapRatio decomposition energy mode
      ≡ ratioOfEnergy coordinate energy

open ModeRatioUsesTransferCoordinate public

positiveSubgapRatioBounds :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    {coordinate : TransferEnergyDecayRatioCoordinate Energy}
    (weld : ModeRatioUsesTransferCoordinate decomposition coordinate)
    energy (mode : R297.SubgapMode family energy) →
  PositiveEnergy coordinate energy →
  StrictlyBelow coordinate energy (candidateEnergy coordinate) →
  (Geo.half < R300.subgapRatio decomposition energy mode)
  × (R300.subgapRatio decomposition energy mode < 1ℚ)
positiveSubgapRatioBounds {decomposition = decomposition} {coordinate = coordinate}
    weld energy mode positive below =
  let
    slowerRaw = strictEnergyOrderReversesDecayRatio coordinate
      energy (candidateEnergy coordinate) below
    slower = ℚP.subst₂
      (λ left right → left < right)
      (ratioOfEnergyOfRatio coordinate Geo.half)
      (sym (modeRatioIsEnergyRatio weld energy mode))
      slowerRaw
    belowOneRaw = positiveEnergyHasStrictDecayRatio coordinate energy positive
    belowOne = subst
      (λ ratio → ratio < 1ℚ)
      (sym (modeRatioIsEnergyRatio weld energy mode))
      belowOneRaw
  in
  slower , belowOne

record SpectrumUsesTransferCoordinate
    {Observable Energy Bound : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    (coordinate : TransferEnergyDecayRatioCoordinate Energy) : Set₁ where
  field
    positiveEnergyIsCoordinatePositive : ∀ energy →
      Gap.PositiveEnergy spectrum energy ≡ PositiveEnergy coordinate energy

    gapCandidateIsCoordinateCandidate :
      Gap.gapCandidate spectrum ≡ candidateEnergy coordinate

open SpectrumUsesTransferCoordinate public

asDecayRatioGapIdentification :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound}
    (coordinate : TransferEnergyDecayRatioCoordinate Energy) →
  SpectrumUsesTransferCoordinate spectrum coordinate →
  R285.DecayRatioGapIdentification spectrum
asDecayRatioGapIdentification {spectrum = spectrum} coordinate weld = record
  { R285.DecayRatioGapIdentification.decayRatio = Geo.half
  ; R285.DecayRatioGapIdentification.decayRatioNonnegative = Geo.halfNonnegative
  ; R285.DecayRatioGapIdentification.decayRatioStrictlyBelowOne =
      R274.halfStrictlyBelowOne
  ; R285.DecayRatioGapIdentification.decayRatioToEnergy = energyOfRatio coordinate
  ; R285.DecayRatioGapIdentification.strictDecayMapsToPositiveEnergy =
      λ ratio nonnegative belowOne →
        subst
          (λ proposition → proposition)
          (sym (positiveEnergyIsCoordinatePositive weld
            (energyOfRatio coordinate ratio)))
          (strictRatioMapsToPositiveEnergy coordinate ratio nonnegative belowOne)
  ; R285.DecayRatioGapIdentification.gapCandidateIsDecayEnergy =
      gapCandidateIsCoordinateCandidate weld
  }

record Round302Boundary : Set where
  constructor round302-boundary
  field
    independentSubgapRateAndCandidateRateSemantics : Bool
    independentSubgapRateAndCandidateRateSemanticsIsFalse :
      independentSubgapRateAndCandidateRateSemantics ≡ false

    oneOrderReversingTransferCoordinateRequired : Bool
    oneOrderReversingTransferCoordinateRequiredIsTrue :
      oneOrderReversingTransferCoordinateRequired ≡ true

    unconditionalSubgapRatioBelowOneIsOverstrong : Bool
    unconditionalSubgapRatioBelowOneIsOverstrongIsTrue :
      unconditionalSubgapRatioBelowOneIsOverstrong ≡ true

    positiveModeRateBoundsCompilerOwned : Bool
    positiveModeRateBoundsCompilerOwnedIsTrue :
      positiveModeRateBoundsCompilerOwned ≡ true

canonicalRound302Boundary : Round302Boundary
canonicalRound302Boundary =
  round302-boundary false refl true refl true refl true refl

round302TransferCoordinateCompilerLevel : ProofLevel
round302TransferCoordinateCompilerLevel = machineChecked

-- Physical OS/transfer-semigroup seam: the selected reconstructed energy order
-- and the decay ratio used by the continuum correlation are one order-reversing
-- coordinate system on the SAME Hamiltonian.
round302PhysicalTransferEnergyDecayCoordinateLevel : ProofLevel
round302PhysicalTransferEnergyDecayCoordinateLevel = conditional
