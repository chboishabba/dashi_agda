module DASHI.Physics.YangMills.ShenZhuZhuGaugeInvariantGaugeFixingBridgeExact where

------------------------------------------------------------------------
-- ROUND68: GAUGE-INVARIANT EXPECTATION/COVARIANCE TRANSPORT
--
-- PRIMARY SOURCE
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "Langevin Dynamics of Lattice Yang--Mills--Higgs and Applications",
-- Communications in Mathematical Physics 407 (2026), Paper 27.
-- DOI: 10.1007/s00220-025-05528-7.
-- arXiv:2401.13299.
--
-- SOURCE MECHANISM
--
-- Section 5.3 uses U-gauge when the Higgs target is the gauge group itself.
-- For every gauge-invariant observable h, Lemma 5.12 identifies its expectation
-- under the original YMH measure with its expectation under the simpler
-- gauge-fixed Gibbs measure.  Corollary 5.14 then transfers exponential
-- covariance decay proved for the gauge-fixed measure back to gauge-invariant
-- observables of the original measure.
--
-- DASHI CONTRIBUTION
--
-- Extract the reusable algebraic consequence: equality of the first moments of
-- F, H and the product FH transports the covariance exactly.  Therefore a
-- future pure-YM gauge-fixing construction does not need to reprove clustering
-- after gauge fixing; it must prove the SAME-OBJECT expectation identities and
-- the decay theorem on the gauge-fixed measure.
--
-- IMPORTANT BOUNDARY
--
-- Pure Yang--Mills has no Higgs field providing the global U-gauge section
-- gx = Phi_x^{-1}.  This module does not manufacture such a section.  It is a
-- safe consumer for an independently constructed pure-YM gauge-fixing / orbit
-- disintegration theorem (for example a source-native local/anchored slice).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _*_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record TwoMeasureMomentTransport (Observable : Set) : Set₁ where
  field
    multiplyObservable : Observable → Observable → Observable
    originalExpectation gaugeFixedExpectation : Observable → ℚ

    GaugeInvariant : Observable → Set

    gaugeInvariantExpectationTransport : ∀ observable →
      GaugeInvariant observable →
      originalExpectation observable ≡ gaugeFixedExpectation observable

    gaugeInvariantClosedUnderProduct : ∀ left right →
      GaugeInvariant left → GaugeInvariant right →
      GaugeInvariant (multiplyObservable left right)

open TwoMeasureMomentTransport public

covariance :
  ∀ {Observable} →
  (Observable → ℚ) →
  (Observable → Observable → Observable) →
  Observable → Observable → ℚ
covariance expectation multiplyObs left right =
  expectation (multiplyObs left right)
  - expectation left * expectation right

gaugeInvariantCovarianceTransport :
  ∀ {Observable}
    (dataSet : TwoMeasureMomentTransport Observable)
    left right →
  GaugeInvariant dataSet left →
  GaugeInvariant dataSet right →
  covariance
    (originalExpectation dataSet)
    (multiplyObservable dataSet) left right
  ≡ covariance
    (gaugeFixedExpectation dataSet)
    (multiplyObservable dataSet) left right
gaugeInvariantCovarianceTransport dataSet left right leftGI rightGI =
  let
    productGI = gaugeInvariantClosedUnderProduct dataSet left right leftGI rightGI
    productEq = gaugeInvariantExpectationTransport dataSet
      (multiplyObservable dataSet left right) productGI
    leftEq = gaugeInvariantExpectationTransport dataSet left leftGI
    rightEq = gaugeInvariantExpectationTransport dataSet right rightGI
  in
  trans
    (cong₂
      (λ productMean leftMean →
        productMean - leftMean * originalExpectation dataSet right)
      productEq leftEq)
    (cong₂
      (λ leftMean rightMean →
        gaugeFixedExpectation dataSet (multiplyObservable dataSet left right)
        - leftMean * rightMean)
      (Agda.Builtin.Equality.refl)
      rightEq)

record GaugeFixedSpatialDecay (Observable : Set) : Set₁ where
  field
    momentTransport : TwoMeasureMomentTransport Observable
    Separation : Observable → Observable → Set
    DecayBound : Observable → Observable → Set
    gaugeFixedDecay : ∀ left right →
      GaugeInvariant momentTransport left →
      GaugeInvariant momentTransport right →
      Separation left right →
      DecayBound left right

    decayBoundDependsOnlyOnGaugeFixedCovariance : ∀ left right →
      covariance
        (originalExpectation momentTransport)
        (multiplyObservable momentTransport) left right
      ≡ covariance
        (gaugeFixedExpectation momentTransport)
        (multiplyObservable momentTransport) left right →
      DecayBound left right → DecayBound left right

open GaugeFixedSpatialDecay public

originalGaugeInvariantDecay :
  ∀ {Observable}
    (dataSet : GaugeFixedSpatialDecay Observable)
    left right →
  GaugeInvariant (momentTransport dataSet) left →
  GaugeInvariant (momentTransport dataSet) right →
  Separation dataSet left right →
  DecayBound dataSet left right
originalGaugeInvariantDecay dataSet left right leftGI rightGI separated =
  decayBoundDependsOnlyOnGaugeFixedCovariance dataSet left right
    (gaugeInvariantCovarianceTransport
      (momentTransport dataSet) left right leftGI rightGI)
    (gaugeFixedDecay dataSet left right leftGI rightGI separated)

gaugeInvariantExpectationTransportAlgebraLevel : ProofLevel
gaugeInvariantExpectationTransportAlgebraLevel = machineChecked

szzYMHUnitaryGaugeSourceLevel : ProofLevel
szzYMHUnitaryGaugeSourceLevel = standardImported

-- A pure-YM consumer still needs an independently justified gauge slice / orbit
-- disintegration whose expectation identity is on the actual Wilson/RG measure.
pureYMGaugeFixingExpectationTransportLevel : ProofLevel
pureYMGaugeFixingExpectationTransportLevel = conditional
