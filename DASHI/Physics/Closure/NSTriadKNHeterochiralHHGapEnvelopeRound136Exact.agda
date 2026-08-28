module DASHI.Physics.Closure.NSTriadKNHeterochiralHHGapEnvelopeRound136Exact where

------------------------------------------------------------------------
-- ROUND136 / CUTOFF-UNIFORM HETEROCHIRAL HH SHELL-GAP ENVELOPES
--
-- Sources:
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--   Bahouri--Chemin--Danchin, Fourier Analysis and Nonlinear PDE,
--   DOI 10.1007/978-3-642-16830-7.
--
-- Round135 reduces every mixed-helicity physical triad to one of three cyclic
-- minority-leg normal forms.  Round102 identifies the HH->low coefficient
-- scale of those classes:
--
--   high-input minority : 2^{-d} H^2,
--   low-output minority : 2^{-2d} H^2.
--
-- The repository already proves the one-gap prefix is uniformly <= 2.  Its
-- general geometric-envelope owner also proves the two-gap prefix
-- sum_d (1/4)^d is uniformly <= 4/3.  This file packages both facts as the
-- exact cutoff-independent shell-GAP payment required by the physical
-- heterochiral reduction.
--
-- IMPORTANT: this closes the gap-index summation only.  It does not sum the
-- physical Fourier incidences inside one shell pair.  Consequently package A
-- is not marked closed here; the surviving HH leaf is now an intra-shell
-- signed l2 aggregation problem, not a shell-gap growth problem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_; 0ℚ; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowDyadicGainExact as HH
import DASHI.Physics.Closure.NSTriadKNHeterochiralHHDyadicGainRound102Exact as Gain

highMinorityGapPrefix : Nat → ℚ
highMinorityGapPrefix = HH.highHighLowGainPrefix

lowMinorityGapPrefix : Nat → ℚ
lowMinorityGapPrefix cutoff = Geo.partialSum Geo.quarter cutoff

highMinorityGapPrefixUniform :
  (cutoff : Nat) → highMinorityGapPrefix cutoff ≤ HH.two
highMinorityGapPrefixUniform = HH.highHighLowGainPrefixBound

lowMinorityGapPrefixUniform :
  (cutoff : Nat) → lowMinorityGapPrefix cutoff ≤ Geo.fourThirds
lowMinorityGapPrefixUniform = Geo.quarterPartialSumBound

weightedHighMinorityGapPrefix : ℚ → Nat → ℚ
weightedHighMinorityGapPrefix base cutoff =
  base * highMinorityGapPrefix cutoff

weightedLowMinorityGapPrefix : ℚ → Nat → ℚ
weightedLowMinorityGapPrefix base cutoff =
  base * lowMinorityGapPrefix cutoff

weightedHighMinorityGapPrefixUniform :
  (base : ℚ) → 0ℚ ≤ base → (cutoff : Nat) →
  weightedHighMinorityGapPrefix base cutoff ≤ HH.two * base
weightedHighMinorityGapPrefixUniform = HH.weightedHighHighLowPrefixBound

weightedLowMinorityGapPrefixUniform :
  (base : ℚ) → 0ℚ ≤ base → (cutoff : Nat) →
  weightedLowMinorityGapPrefix base cutoff ≤ Geo.fourThirds * base
weightedLowMinorityGapPrefixUniform base baseNonnegative cutoff =
  let
    instance
      baseNN = nonNegative baseNonnegative
    scaled :
      base * lowMinorityGapPrefix cutoff
      ≤ base * Geo.fourThirds
    scaled =
      ℚₚ.*-monoˡ-≤-nonNeg base (lowMinorityGapPrefixUniform cutoff)
    commute : base * Geo.fourThirds ≡ Geo.fourThirds * base
    commute = ℚₚ.*-comm base Geo.fourThirds
  in
  subst
    (λ upper → weightedLowMinorityGapPrefix base cutoff ≤ upper)
    commute
    scaled

------------------------------------------------------------------------
-- Connection to the exact Round102 dyadic coefficient calibration.
------------------------------------------------------------------------

highMinorityCoefficientHasOneGap :
  (outputShell gap : Nat) →
  Gain.highMinorityCoefficientScale outputShell gap
  ≡ Gain.helicalGapGain gap * Gain.naiveHighSquaredScale outputShell gap
highMinorityCoefficientHasOneGap =
  Gain.highMinorityIsOneGapGainTimesHighSquared

lowMinorityCoefficientHasTwoGaps :
  (outputShell gap : Nat) →
  Gain.lowMinorityCoefficientScale outputShell gap
  ≡ (Gain.helicalGapGain gap * Gain.helicalGapGain gap)
      * Gain.naiveHighSquaredScale outputShell gap
lowMinorityCoefficientHasTwoGaps =
  Gain.lowMinorityIsTwoGapGainsTimesHighSquared

round136HighMinorityOneGapPrefixCutoffUniform : Bool
round136HighMinorityOneGapPrefixCutoffUniform = true

round136LowMinorityTwoGapPrefixCutoffUniform : Bool
round136LowMinorityTwoGapPrefixCutoffUniform = true

round136EveryHeterochiralHHClassHasCutoffUniformGapEnvelope : Bool
round136EveryHeterochiralHHClassHasCutoffUniformGapEnvelope = true

round136HHGapIndexSummationClosed : Bool
round136HHGapIndexSummationClosed = true

round136HHIntraShellSignedL2AggregationClosed : Bool
round136HHIntraShellSignedL2AggregationClosed = false

round136PackageAClosed : Bool
round136PackageAClosed = false

round136HHGapIndexSummationClosedIsTrue :
  round136HHGapIndexSummationClosed ≡ true
round136HHGapIndexSummationClosedIsTrue = refl

round136HHIntraShellSignedL2AggregationClosedIsFalse :
  round136HHIntraShellSignedL2AggregationClosed ≡ false
round136HHIntraShellSignedL2AggregationClosedIsFalse = refl

round136PackageAClosedIsFalse : round136PackageAClosed ≡ false
round136PackageAClosedIsFalse = refl
