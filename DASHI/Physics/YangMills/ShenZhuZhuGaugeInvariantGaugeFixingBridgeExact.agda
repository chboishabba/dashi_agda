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
-- Equality of the first moments of F,H and FH transports covariance exactly.
-- A future pure-YM gauge-fixing construction therefore need not reprove
-- clustering after gauge fixing; it must prove the SAME-OBJECT expectation
-- identities and the decay theorem on the gauge-fixed measure.
--
-- IMPORTANT BOUNDARY
--
-- Pure Yang--Mills has no Higgs field providing the global U-gauge section
-- gx = Phi_x^{-1}.  This module does not manufacture such a section.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_; _-_)

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
gaugeInvariantCovarianceTransport dataSet left right leftGI rightGI
  rewrite gaugeInvariantExpectationTransport dataSet
            (multiplyObservable dataSet left right)
            (gaugeInvariantClosedUnderProduct dataSet left right leftGI rightGI)
        | gaugeInvariantExpectationTransport dataSet left leftGI
        | gaugeInvariantExpectationTransport dataSet right rightGI = refl

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

    decayBoundTransport : ∀ left right →
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
  decayBoundTransport dataSet left right
    (gaugeInvariantCovarianceTransport
      (momentTransport dataSet) left right leftGI rightGI)
    (gaugeFixedDecay dataSet left right leftGI rightGI separated)

gaugeInvariantExpectationTransportAlgebraLevel : ProofLevel
gaugeInvariantExpectationTransportAlgebraLevel = machineChecked

szzYMHUnitaryGaugeSourceLevel : ProofLevel
szzYMHUnitaryGaugeSourceLevel = standardImported

pureYMGaugeFixingExpectationTransportLevel : ProofLevel
pureYMGaugeFixingExpectationTransportLevel = conditional
