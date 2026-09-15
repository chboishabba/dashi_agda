module DASHI.Physics.Closure.NSTriadKNTwoShellLowRemoteEuclideanGapExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b2c1 / TWO-SHELL LOW-REMOTE EUCLIDEAN GAP
--
-- After the exact three-region split, the coercive R98 route must compare only
--
--   low    : shellIndex < suc K
--   remote : suc (suc K) <= shellIndex.
--
-- The literal max-norm dyadic geometry then gives
--
--   |low|_2^2    <= 3 * (2^K)^2,
--   4 * (2^K)^2 <= |remote|_2^2.
--
-- Thus the dimension-three Euclidean comparison constant is strictly dominated
-- by the factor-four dyadic separation.  This file pays only that finite
-- frequency geometry.  It does NOT yet construct packet energies/dissipations
-- or the R98 SpectralCrossDissipationDatum.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_; _<_; _∸_; z≤n; s≤s)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNCeilLogShellBounds as Ceil
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNDyadicEuclideanShellMarginRound88Exact as R88

------------------------------------------------------------------------
-- Tiny Nat helpers.
------------------------------------------------------------------------

dropOneFromTwoShellSeparation :
  ∀ {K J} → suc (suc K) ≤ J → suc K ≤ J ∸ 1
dropOneFromTwoShellSeparation {J = zero} ()
dropOneFromTwoShellSeparation {J = suc J} (s≤s separated) = separated

twoShellSeparationForcesPositiveHighShell :
  ∀ {K J} → suc (suc K) ≤ J → 0 < J
twoShellSeparationForcesPositiveHighShell {J = zero} ()
twoShellSeparationForcesPositiveHighShell {J = suc J} separated = s≤s z≤n

pow2Successor : ∀ K → Shell.pow2 (suc K) ≡ 2 * Shell.pow2 K
pow2Successor K = refl

pow2SuccessorSquareIsFourTimes : ∀ K →
  R88.natSquare (Shell.pow2 (suc K))
  ≡ 4 * R88.natSquare (Shell.pow2 K)
pow2SuccessorSquareIsFourTimes K =
  trans
    (cong R88.natSquare (pow2Successor K))
    (R88.doubleSquareIsFourSquare (Shell.pow2 K))

threeBelowFourScaledSquare : ∀ n →
  3 * R88.natSquare n ≤ 4 * R88.natSquare n
threeBelowFourScaledSquare n =
  Nat.*-mono-≤
    (s≤s (s≤s (s≤s z≤n)))
    Nat.≤-refl

------------------------------------------------------------------------
-- Modewise low ceiling and remote floor.
------------------------------------------------------------------------

lowModeFrequencyCeiling :
  ∀ {k K} →
  Shell.shellIndex k < suc K →
  ModeNorm.modeNatNormSquared k
  ≤ 3 * R88.natSquare (Shell.pow2 K)
lowModeFrequencyCeiling {k} {K} (s≤s shell≤K) =
  R88.modeNatNormBelowPacketThreeSquare shell≤K

remoteModeFrequencyFloor :
  ∀ {p K} →
  suc (suc K) ≤ Shell.shellIndex p →
  4 * R88.natSquare (Shell.pow2 K)
  ≤ ModeNorm.modeNatNormSquared p
remoteModeFrequencyFloor {p} {K} separated =
  let
    exponentBelow :
      suc K ≤ Shell.shellIndex p ∸ 1
    exponentBelow = dropOneFromTwoShellSeparation separated

    powerBelowLowerShell :
      Shell.pow2 (suc K)
      ≤ Shell.pow2 (Shell.shellIndex p ∸ 1)
    powerBelowLowerShell = R88.pow2Monotone exponentBelow

    highShellPositive : 0 < Shell.shellIndex p
    highShellPositive = twoShellSeparationForcesPositiveHighShell separated

    lowerStrict :
      Shell.pow2 (Shell.shellIndex p ∸ 1)
      < Infinity.infinityNorm p
    lowerStrict =
      Ceil.ceilLogShellLowerMagnitude
        (Infinity.infinityNorm p) highShellPositive

    successorPowerBelowInfinity :
      Shell.pow2 (suc K) ≤ Infinity.infinityNorm p
    successorPowerBelowInfinity =
      Nat.<⇒≤ (Nat.≤-<-trans powerBelowLowerShell lowerStrict)

    squared :
      R88.natSquare (Shell.pow2 (suc K))
      ≤ R88.natSquare (Infinity.infinityNorm p)
    squared = R88.squareMonotone successorPowerBelowInfinity

    toMode :
      R88.natSquare (Shell.pow2 (suc K))
      ≤ ModeNorm.modeNatNormSquared p
    toMode =
      Nat.≤-trans squared (R88.infinitySquareBelowModeNatNorm p)
  in
  subst
    (λ lower → lower ≤ ModeNorm.modeNatNormSquared p)
    (pow2SuccessorSquareIsFourTimes K)
    toMode

lowCeilingBelowRemoteFloor : ∀ K →
  3 * R88.natSquare (Shell.pow2 K)
  ≤ 4 * R88.natSquare (Shell.pow2 K)
lowCeilingBelowRemoteFloor K =
  threeBelowFourScaledSquare (Shell.pow2 K)

record TwoShellLowRemoteFrequencyGap
    (low remote : Z3.FourierMode)
    (K : Nat) : Set where
  constructor two-shell-low-remote-frequency-gap
  field
    lowShell : Shell.shellIndex low < suc K
    remoteShell : suc (suc K) ≤ Shell.shellIndex remote
    lowFrequencyUpper :
      ModeNorm.modeNatNormSquared low
      ≤ 3 * R88.natSquare (Shell.pow2 K)
    remoteFrequencyLower :
      4 * R88.natSquare (Shell.pow2 K)
      ≤ ModeNorm.modeNatNormSquared remote
    separatedCeilingFloor :
      3 * R88.natSquare (Shell.pow2 K)
      ≤ 4 * R88.natSquare (Shell.pow2 K)

open TwoShellLowRemoteFrequencyGap public

buildTwoShellLowRemoteFrequencyGap :
  (low remote : Z3.FourierMode) →
  (K : Nat) →
  Shell.shellIndex low < suc K →
  suc (suc K) ≤ Shell.shellIndex remote →
  TwoShellLowRemoteFrequencyGap low remote K
buildTwoShellLowRemoteFrequencyGap low remote K lowShell remoteShell = record
  { lowShell = lowShell
  ; remoteShell = remoteShell
  ; lowFrequencyUpper = lowModeFrequencyCeiling lowShell
  ; remoteFrequencyLower = remoteModeFrequencyFloor remoteShell
  ; separatedCeilingFloor = lowCeilingBelowRemoteFloor K
  }

------------------------------------------------------------------------
-- Status / next exact leaf.
------------------------------------------------------------------------

lowFrequencyCeilingClosed : Bool
lowFrequencyCeilingClosed = true

remoteFrequencyFloorClosed : Bool
remoteFrequencyFloorClosed = true

literalLowRemoteSpectralDatumConstructed : Bool
literalLowRemoteSpectralDatumConstructed = false

lowFrequencyCeilingClosedIsTrue : lowFrequencyCeilingClosed ≡ true
lowFrequencyCeilingClosedIsTrue = refl

remoteFrequencyFloorClosedIsTrue : remoteFrequencyFloorClosed ≡ true
remoteFrequencyFloorClosedIsTrue = refl

literalLowRemoteSpectralDatumConstructedIsFalse :
  literalLowRemoteSpectralDatumConstructed ≡ false
literalLowRemoteSpectralDatumConstructedIsFalse = refl
