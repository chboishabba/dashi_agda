{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound294Exact where

------------------------------------------------------------------------
-- ROUND294 / D3 = PHYSICAL RATE SEMANTICS + GENERIC GEOMETRIC DOMINANCE
--
-- R288 asks for one separating time for every alleged positive subgap mode.
-- Once the reconstructed envelopes are geometric, that time is not a fresh
-- Yang--Mills theorem.  The direct CMP116 route has fast ratio 1/2.  A positive
-- subgap mode supplies a slower ratio q_E, positive amplitude B_E, and the
-- physical identification of its spectral lower envelope.  Source-independent
-- rational geometric dominance then produces one finite separating time.
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
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanSubgapSeparatingTimeRound288Exact as R288
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSReconstructionCyclicityExact as Cyclic
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

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
separatingWitness {core = core} dominance semantics energy mode positive below =
  let
    observable =
      Cyclic.modeObservableFromCyclicity
        (R288.subgapMeaning core) energy mode
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
    fastEq = clusteringEnvelopeIsFastGeometric semantics observable time
    slowEq = subgapEnvelopeIsSlowGeometric semantics energy mode time
  in
  time ,
    subst
      (λ fast → fast < R288.subgapSpectralEnvelope core energy observable time)
      (symEq fastEq)
      (subst
        (λ slow →
          fastAmplitude semantics observable * Power.rationalPower Geo.half time
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

record Round294Boundary : Set where
  constructor round294-boundary
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

canonicalRound294Boundary : Round294Boundary
canonicalRound294Boundary =
  round294-boundary false refl true refl true refl true refl true refl

round294SeparatingTimeCompilerLevel : ProofLevel
round294SeparatingTimeCompilerLevel = machineChecked

round294RationalGeometricDominanceLevel : ProofLevel
round294RationalGeometricDominanceLevel = standardImported

round294PhysicalSubgapRateSemanticsLevel : ProofLevel
round294PhysicalSubgapRateSemanticsLevel = conditional
