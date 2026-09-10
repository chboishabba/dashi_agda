{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact where

------------------------------------------------------------------------
-- ROUND293 / D3 = PHYSICAL RATE SEMANTICS + GENERIC GEOMETRIC DOMINANCE
--
-- R288 asks for one separating time for every alleged positive subgap mode.
-- That should not be charged as one opaque Yang--Mills theorem once the
-- reconstructed spectral envelopes are genuinely exponential/geometric.
--
-- On the direct CMP116 route the fast clustering ratio is exactly 1/2.  A
-- positive mode strictly below the candidate energy must therefore be given a
-- slower ratio q_E with
--
--     1/2 < q_E < 1
--
-- and a positive overlap amplitude B_E.  If the physical spectral lower
-- envelope is B_E q_E^t while the clustering envelope is A (1/2)^t, then the
-- only remaining source-independent step is ordinary Archimedean geometric
-- domination: for some finite t,
--
--     A (1/2)^t < B_E q_E^t.
--
-- This module keeps that arithmetic authority separate from the physical
-- energy/rate and overlap-amplitude semantics, and compiles both into R288's
-- exact separating-time receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanSubgapSeparatingTimeRound288Exact as R288
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSReconstructionCyclicityExact as Cyclic
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

------------------------------------------------------------------------
-- Source-independent rational geometric authority.
------------------------------------------------------------------------

record RationalGeometricDominance : Set₁ where
  field
    eventuallySlowDominatesFast :
      (fastAmplitude slowAmplitude slowRatio : ℚ) →
      0ℚ ≤ fastAmplitude →
      0ℚ < slowAmplitude →
      Geo.half < slowRatio →
      slowRatio < 1ℚ →
      Σ Nat (λ time →
        fastAmplitude * Power.rationalPower Geo.half time
        < slowAmplitude * Power.rationalPower slowRatio time)

open RationalGeometricDominance public

------------------------------------------------------------------------
-- Physical spectral-rate realization on the pre-rate continuum spectrum.
------------------------------------------------------------------------

record SubgapGeometricRateSemantics
    {Measure TestObservable Energy Vector : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    (core : R288.CyclicCovarianceSpectralCore dataSet extension tests) : Set₁ where
  field
    fastAmplitude : TestObservable → ℚ

    subgapAmplitude :
      ∀ energy → Cyclic.SubgapMode (R288.subgapVectors core) energy → ℚ
    subgapRatio :
      ∀ energy → Cyclic.SubgapMode (R288.subgapVectors core) energy → ℚ

    fastAmplitudeNonnegative : ∀ observable →
      0ℚ ≤ fastAmplitude observable

    subgapAmplitudePositive :
      ∀ energy mode →
      R288.PositiveEnergy core energy →
      R288.StrictlyBelow core energy (R288.gapCandidate core) →
      0ℚ < subgapAmplitude energy mode

    positiveSubgapHasSlowerRatio :
      ∀ energy mode →
      R288.PositiveEnergy core energy →
      R288.StrictlyBelow core energy (R288.gapCandidate core) →
      Geo.half < subgapRatio energy mode

    subgapRatioStrictlyBelowOne :
      ∀ energy mode → subgapRatio energy mode < 1ℚ

    clusteringEnvelopeIsFastGeometric : ∀ observable time →
      R288.clusteringEnvelope core observable time
      ≡ fastAmplitude observable * Power.rationalPower Geo.half time

    subgapEnvelopeIsSlowGeometric : ∀ energy mode time →
      let observable =
            Cyclic.modeObservableFromCyclicity
              (R288.subgapMeaning core) energy mode
      in
      R288.subgapSpectralEnvelope core energy observable time
      ≡ subgapAmplitude energy mode
          * Power.rationalPower (subgapRatio energy mode) time

open SubgapGeometricRateSemantics public

------------------------------------------------------------------------
-- Compiler into R288.
------------------------------------------------------------------------

separatingWitness :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {core : R288.CyclicCovarianceSpectralCore dataSet extension tests} →
  RationalGeometricDominance →
  SubgapGeometricRateSemantics core →
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
separatingWitness dominance semantics energy mode positive below =
  let
    observable =
      Cyclic.modeObservableFromCyclicity
        (R288.subgapMeaning _) energy mode
    raw = eventuallySlowDominatesFast dominance
      (fastAmplitude semantics observable)
      (subgapAmplitude semantics energy mode)
      (subgapRatio semantics energy mode)
      (fastAmplitudeNonnegative semantics observable)
      (subgapAmplitudePositive semantics energy mode positive below)
      (positiveSubgapHasSlowerRatio semantics energy mode positive below)
      (subgapRatioStrictlyBelowOne semantics energy mode)
    time = fst raw
    strict = snd raw
  in
  time ,
    ℚP.subst₂
      (λ left right → left < right)
      (clusteringEnvelopeIsFastGeometric semantics observable time)
      (subgapEnvelopeIsSlowGeometric semantics energy mode time)
      strict

-- Rational order contradiction: lower <= correlation <= upper but upper < lower.
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
  RationalGeometricDominance →
  SubgapGeometricRateSemantics core →
  R288.SubgapSeparatingTimeData core
asSubgapSeparatingTimeData dominance semantics = record
  { R288.SubgapSeparatingTimeData.separatingTime =
      λ energy mode positive below →
        fst (separatingWitness dominance semantics energy mode positive below)
  ; R288.SubgapSeparatingTimeData.lowerAndUpperContradictAtSeparatingTime =
      λ energy mode positive below lower≤correlation correlation≤upper →
        let
          strict = snd
            (separatingWitness dominance semantics energy mode positive below)
        in
        strictSandwichImpossible lower≤correlation correlation≤upper strict
  }

------------------------------------------------------------------------
-- Introspective boundary.
------------------------------------------------------------------------

record Round293Boundary : Set where
  constructor round293-boundary
  field
    opaqueYMSeparatingTimePrimitive : Bool
    opaqueYMSeparatingTimePrimitiveIsFalse :
      opaqueYMSeparatingTimePrimitive ≡ false

    physicalSubgapRateOrderingRequired : Bool
    physicalSubgapRateOrderingRequiredIsTrue :
      physicalSubgapRateOrderingRequired ≡ true

    physicalPositiveOverlapAmplitudeRequired : Bool
    physicalPositiveOverlapAmplitudeRequiredIsTrue :
      physicalPositiveOverlapAmplitudeRequired ≡ true

    genericGeometricDominanceSourceIndependent : Bool
    genericGeometricDominanceSourceIndependentIsTrue :
      genericGeometricDominanceSourceIndependent ≡ true

    separatingTimeAfterRatesCompilerOwned : Bool
    separatingTimeAfterRatesCompilerOwnedIsTrue :
      separatingTimeAfterRatesCompilerOwned ≡ true

canonicalRound293Boundary : Round293Boundary
canonicalRound293Boundary =
  round293-boundary false refl true refl true refl true refl true refl

round293SeparatingTimeCompilerLevel : ProofLevel
round293SeparatingTimeCompilerLevel = machineChecked

-- Standard Archimedean/geometric-series arithmetic.  This is not a Yang--Mills
-- research estimate, but an exact local theorem/import is still required before
-- promotion.
round293RationalGeometricDominanceLevel : ProofLevel
round293RationalGeometricDominanceLevel = standardImported

-- Physical spectral semantics that remain after the arithmetic is factored out.
round293PhysicalSubgapRateSemanticsLevel : ProofLevel
round293PhysicalSubgapRateSemanticsLevel = conditional
