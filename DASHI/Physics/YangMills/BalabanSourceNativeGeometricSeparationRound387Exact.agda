{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSourceNativeGeometricSeparationRound387Exact where

------------------------------------------------------------------------
-- ROUND387 / SOURCE-NATIVE FAST DECAY RATIO
--
-- The historical direct CMP116 spectral route specializes the fast clustering
-- envelope to
--
--     A_fast * (1/2)^t.
--
-- That is a convenient consequence of the configured 8/16 KP rooted shell, but
-- it is stronger than the spectral contradiction requires.  CMP116 (1.29)
-- carries its own positive exponential source rate.  The terminal comparison
-- only needs a fast geometric ratio strictly below the alleged subgap ratio.
--
-- This owner therefore removes `1/2` from the generic spectral-comparison ABI:
--
--   0 <= q_fast < q_slow < 1
--   + A_fast >= 0
--   + A_slow > 0
--   -------------------------------------------------
--   eventually A_fast q_fast^t < A_slow q_slow^t.
--
-- The eventual-dominance theorem is source-independent standard analysis.  No
-- Yang--Mills estimate is manufactured here.  The physical/source work is now
-- allowed to retain the source-native q_fast instead of first strengthening it
-- to the repository's configured `1/2` shell.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanSubgapSeparatingTimeRound288Exact as R288
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSReconstructionCyclicityExact as Cyclic
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

------------------------------------------------------------------------
-- Source-independent geometric dominance, with BOTH ratios explicit.
------------------------------------------------------------------------

record TwoRatioRationalGeometricDominance : Set₁ where
  field
    eventuallySlowDominatesFast :
      (fastAmplitude slowAmplitude fastRatio slowRatio : ℚ) →
      0ℚ ≤ fastAmplitude →
      0ℚ < slowAmplitude →
      0ℚ ≤ fastRatio →
      fastRatio < slowRatio →
      slowRatio < 1ℚ →
      Σ Nat (λ time →
        fastAmplitude * Power.rationalPower fastRatio time
        < slowAmplitude * Power.rationalPower slowRatio time)

open TwoRatioRationalGeometricDominance public

------------------------------------------------------------------------
-- Same reconstructed spectral consumer as R294, but no fixed fast ratio.
------------------------------------------------------------------------

record SourceNativeSubgapGeometricRateSemantics
    {Measure TestObservable Energy Vector : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    (core : R288.CyclicCovarianceSpectralCore dataSet extension tests) : Set₁ where
  field
    fastAmplitude : TestObservable → ℚ
    fastRatio : ℚ

    subgapAmplitude :
      ∀ energy → Cyclic.SubgapMode (R288.subgapVectors core) energy → ℚ
    subgapRatio :
      ∀ energy → Cyclic.SubgapMode (R288.subgapVectors core) energy → ℚ

    fastAmplitudeNonnegative : ∀ observable →
      0ℚ ≤ fastAmplitude observable
    fastRatioNonnegative : 0ℚ ≤ fastRatio

    subgapAmplitudePositive :
      ∀ energy mode →
      R288.PositiveEnergy core energy →
      R288.StrictlyBelow core energy (R288.gapCandidate core) →
      0ℚ < subgapAmplitude energy mode

    positiveSubgapHasSlowerRatio :
      ∀ energy mode →
      R288.PositiveEnergy core energy →
      R288.StrictlyBelow core energy (R288.gapCandidate core) →
      fastRatio < subgapRatio energy mode

    subgapRatioStrictlyBelowOne :
      ∀ energy mode → subgapRatio energy mode < 1ℚ

    clusteringEnvelopeIsSourceNativeGeometric : ∀ observable time →
      R288.clusteringEnvelope core observable time
      ≡ fastAmplitude observable * Power.rationalPower fastRatio time

    subgapEnvelopeIsSlowGeometric : ∀ energy mode time →
      let observable =
            Cyclic.modeObservableFromCyclicity
              (R288.subgapMeaning core) energy mode
      in
      R288.subgapSpectralEnvelope core energy observable time
      ≡ subgapAmplitude energy mode
          * Power.rationalPower (subgapRatio energy mode) time

open SourceNativeSubgapGeometricRateSemantics public

separatingWitness :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {core : R288.CyclicCovarianceSpectralCore dataSet extension tests} →
  TwoRatioRationalGeometricDominance →
  SourceNativeSubgapGeometricRateSemantics core →
  ∀ energy (mode : Cyclic.SubgapMode (R288.subgapVectors core) energy) →
  R288.PositiveEnergy core energy →
  R288.StrictlyBelow core energy (R288.gapCandidate core) →
  Σ Nat (λ time →
    let observable =
          Cyclic.modeObservableFromCyclicity
            (R288.subgapMeaning core) energy mode
    in
    R288.clusteringEnvelope core observable time
    < R288.subgapSpectralEnvelope core energy observable time)
separatingWitness {core = core} dominance semantics energy mode positive below =
  let
    observable =
      Cyclic.modeObservableFromCyclicity
        (R288.subgapMeaning core) energy mode
    raw = eventuallySlowDominatesFast dominance
      (fastAmplitude semantics observable)
      (subgapAmplitude semantics energy mode)
      (fastRatio semantics)
      (subgapRatio semantics energy mode)
      (fastAmplitudeNonnegative semantics observable)
      (subgapAmplitudePositive semantics energy mode positive below)
      (fastRatioNonnegative semantics)
      (positiveSubgapHasSlowerRatio semantics energy mode positive below)
      (subgapRatioStrictlyBelowOne semantics energy mode)
    time = fst raw
    strict = snd raw
    fastEq = clusteringEnvelopeIsSourceNativeGeometric semantics observable time
    slowEq = subgapEnvelopeIsSlowGeometric semantics energy mode time
  in
  time ,
    subst
      (λ fast → fast < R288.subgapSpectralEnvelope core energy observable time)
      (symEq fastEq)
      (subst
        (λ slow →
          fastAmplitude semantics observable
            * Power.rationalPower (fastRatio semantics) time
          < slow)
        (symEq slowEq)
        strict)
  where
  symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  symEq refl = refl

strictSandwichImpossible :
  ∀ {lower correlation upper : ℚ} →
  lower ≤ correlation → correlation ≤ upper → upper < lower → Gap.Empty
strictSandwichImpossible lower≤correlation correlation≤upper upper<lower =
  let
    lower≤upper = ℚP.≤-trans lower≤correlation correlation≤upper
    upper<upper = ℚP.<-≤-trans upper<lower lower≤upper
    impossible : ⊥
    impossible = (ℚP.<-irrefl _) upper<upper
  in
  ⊥-elim impossible

asSubgapSeparatingTimeData :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {core : R288.CyclicCovarianceSpectralCore dataSet extension tests} →
  TwoRatioRationalGeometricDominance →
  SourceNativeSubgapGeometricRateSemantics core →
  R288.SubgapSeparatingTimeData core
asSubgapSeparatingTimeData dominance semantics = record
  { R288.SubgapSeparatingTimeData.separatingTime =
      λ energy mode positive below →
        fst (separatingWitness dominance semantics energy mode positive below)
  ; R288.SubgapSeparatingTimeData.lowerAndUpperContradictAtSeparatingTime =
      λ energy mode positive below lower≤correlation correlation≤upper →
        let strict = snd
              (separatingWitness dominance semantics energy mode positive below)
        in strictSandwichImpossible lower≤correlation correlation≤upper strict
  }

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round387TwoRatioSeparationCompilerLevel : ProofLevel
round387TwoRatioSeparationCompilerLevel = machineChecked

round387GenericGeometricDominanceLevel : ProofLevel
round387GenericGeometricDominanceLevel = standardImported

fixedHalfRatioMandatoryForSpectralContradiction : Bool
fixedHalfRatioMandatoryForSpectralContradiction = false

fixedHalfRatioMandatoryForSpectralContradictionIsFalse :
  fixedHalfRatioMandatoryForSpectralContradiction ≡ false
fixedHalfRatioMandatoryForSpectralContradictionIsFalse = refl

sourceNativeFastRatioMayBeRetained : Bool
sourceNativeFastRatioMayBeRetained = true

sourceNativeFastRatioMayBeRetainedIsTrue :
  sourceNativeFastRatioMayBeRetained ≡ true
sourceNativeFastRatioMayBeRetainedIsTrue = refl

sourceNativeRatioStillNeedsPhysicalTimeCalibration : Bool
sourceNativeRatioStillNeedsPhysicalTimeCalibration = true

sourceNativeRatioStillNeedsPhysicalTimeCalibrationIsTrue :
  sourceNativeRatioStillNeedsPhysicalTimeCalibration ≡ true
sourceNativeRatioStillNeedsPhysicalTimeCalibrationIsTrue = refl

sourceNativeRatioStillNeedsSpectrumRateIdentification : Bool
sourceNativeRatioStillNeedsSpectrumRateIdentification = true

sourceNativeRatioStillNeedsSpectrumRateIdentificationIsTrue :
  sourceNativeRatioStillNeedsSpectrumRateIdentification ≡ true
sourceNativeRatioStillNeedsSpectrumRateIdentificationIsTrue = refl

record Round387Boundary : Set where
  constructor round387-boundary
  field
    halfSpecificKPRouteRemainsValidSpecialization : Bool
    halfSpecificKPRouteRemainsValidSpecializationIsTrue :
      halfSpecificKPRouteRemainsValidSpecialization ≡ true

    fixedHalfNoLongerPrimitiveForDirectCMP116Route : Bool
    fixedHalfNoLongerPrimitiveForDirectCMP116RouteIsTrue :
      fixedHalfNoLongerPrimitiveForDirectCMP116Route ≡ true

    selectedAbsoluteLocalizationStillProofBearing : Bool
    selectedAbsoluteLocalizationStillProofBearingIsTrue :
      selectedAbsoluteLocalizationStillProofBearing ≡ true

canonicalRound387Boundary : Round387Boundary
canonicalRound387Boundary =
  round387-boundary true refl true refl true refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
