module DASHI.Biology.TernaryPhaseQuotientJCoarseBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Ingrid Daubechies,
-- "Ten Lectures on Wavelets", SIAM, 1992.
-- DOI: 10.1137/1.9781611970104.
--
-- DASHI CONTRIBUTION
--
-- Identify the already-constructed C3 output-phase quotient of the 27
-- ternary endomorphisms with the ordinary nine-channel jCoarse carrier.
-- This is a two-sided carrier equivalence, not a cardinality comparison:
--
--   (T^T / C3)  =  T x T  <->  BalancedTrit x BalancedTrit.
--
-- The distinguished completion channel j is deliberately not part of this
-- nine-state equivalence; it is adjoined only after the ordinary quotient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

import Base369 as Base
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.JFineCoarseRelativeScaleExact as Scale
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase

triToBalanced : Base.TriTruth → Harmonic.BalancedTrit
triToBalanced Base.tri-low = Harmonic.negativeTrit
triToBalanced Base.tri-mid = Harmonic.zeroTrit
triToBalanced Base.tri-high = Harmonic.positiveTrit

balancedToTri : Harmonic.BalancedTrit → Base.TriTruth
balancedToTri Harmonic.negativeTrit = Base.tri-low
balancedToTri Harmonic.zeroTrit = Base.tri-mid
balancedToTri Harmonic.positiveTrit = Base.tri-high

balancedAfterTri :
  (value : Base.TriTruth) →
  balancedToTri (triToBalanced value) ≡ value
balancedAfterTri Base.tri-low = refl
balancedAfterTri Base.tri-mid = refl
balancedAfterTri Base.tri-high = refl

triAfterBalanced :
  (value : Harmonic.BalancedTrit) →
  triToBalanced (balancedToTri value) ≡ value
triAfterBalanced Harmonic.negativeTrit = refl
triAfterBalanced Harmonic.zeroTrit = refl
triAfterBalanced Harmonic.positiveTrit = refl

phaseQuotientToBalancedPair :
  Phase.PhaseQuotient9 → Harmonic.BalancedPair
phaseQuotientToBalancedPair (left , right) =
  Harmonic.balancedPair (triToBalanced left) (triToBalanced right)

balancedPairToPhaseQuotient :
  Harmonic.BalancedPair → Phase.PhaseQuotient9
balancedPairToPhaseQuotient
  (Harmonic.balancedPair left right) =
  balancedToTri left , balancedToTri right

phaseQuotientRoundTrip :
  (pair : Phase.PhaseQuotient9) →
  balancedPairToPhaseQuotient
    (phaseQuotientToBalancedPair pair) ≡ pair
phaseQuotientRoundTrip (Base.tri-low , Base.tri-low) = refl
phaseQuotientRoundTrip (Base.tri-low , Base.tri-mid) = refl
phaseQuotientRoundTrip (Base.tri-low , Base.tri-high) = refl
phaseQuotientRoundTrip (Base.tri-mid , Base.tri-low) = refl
phaseQuotientRoundTrip (Base.tri-mid , Base.tri-mid) = refl
phaseQuotientRoundTrip (Base.tri-mid , Base.tri-high) = refl
phaseQuotientRoundTrip (Base.tri-high , Base.tri-low) = refl
phaseQuotientRoundTrip (Base.tri-high , Base.tri-mid) = refl
phaseQuotientRoundTrip (Base.tri-high , Base.tri-high) = refl

balancedPairRoundTrip :
  (pair : Harmonic.BalancedPair) →
  phaseQuotientToBalancedPair
    (balancedPairToPhaseQuotient pair) ≡ pair
balancedPairRoundTrip
  (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.negativeTrit) = refl
balancedPairRoundTrip
  (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.zeroTrit) = refl
balancedPairRoundTrip
  (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.positiveTrit) = refl
balancedPairRoundTrip
  (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.negativeTrit) = refl
balancedPairRoundTrip
  (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.zeroTrit) = refl
balancedPairRoundTrip
  (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.positiveTrit) = refl
balancedPairRoundTrip
  (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.negativeTrit) = refl
balancedPairRoundTrip
  (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.zeroTrit) = refl
balancedPairRoundTrip
  (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.positiveTrit) = refl

phaseQuotientToOrdinaryCoarse :
  Phase.PhaseQuotient9 → Harmonic.CoarseChannel
phaseQuotientToOrdinaryCoarse pair =
  Harmonic.ordinaryChannel (phaseQuotientToBalancedPair pair)

data OrdinaryCoarseChannel : Set where
  ordinary :
    Harmonic.BalancedPair → OrdinaryCoarseChannel

ordinaryToCoarse :
  OrdinaryCoarseChannel → Harmonic.CoarseChannel
ordinaryToCoarse (ordinary pair) = Harmonic.ordinaryChannel pair

phaseQuotientToOrdinary :
  Phase.PhaseQuotient9 → OrdinaryCoarseChannel
phaseQuotientToOrdinary pair =
  ordinary (phaseQuotientToBalancedPair pair)

ordinaryToPhaseQuotient :
  OrdinaryCoarseChannel → Phase.PhaseQuotient9
ordinaryToPhaseQuotient (ordinary pair) =
  balancedPairToPhaseQuotient pair

ordinaryPhaseRoundTrip :
  (pair : Phase.PhaseQuotient9) →
  ordinaryToPhaseQuotient (phaseQuotientToOrdinary pair) ≡ pair
ordinaryPhaseRoundTrip = phaseQuotientRoundTrip

phaseOrdinaryRoundTrip :
  (channel : OrdinaryCoarseChannel) →
  phaseQuotientToOrdinary (ordinaryToPhaseQuotient channel) ≡ channel
phaseOrdinaryRoundTrip (ordinary pair)
  rewrite balancedPairRoundTrip pair = refl

jCoarseCountMatchesPhaseQuotient : Scale.jCoarseFrequency ≡ 9
jCoarseCountMatchesPhaseQuotient = refl

record PhaseQuotientJCoarseEquivalence : Set where
  field
    toOrdinary : Phase.PhaseQuotient9 → OrdinaryCoarseChannel
    fromOrdinary : OrdinaryCoarseChannel → Phase.PhaseQuotient9
    fromAfterTo :
      (pair : Phase.PhaseQuotient9) →
      fromOrdinary (toOrdinary pair) ≡ pair
    toAfterFrom :
      (channel : OrdinaryCoarseChannel) →
      toOrdinary (fromOrdinary channel) ≡ channel

canonicalPhaseQuotientJCoarseEquivalence :
  PhaseQuotientJCoarseEquivalence
canonicalPhaseQuotientJCoarseEquivalence =
  record
    { toOrdinary = phaseQuotientToOrdinary
    ; fromOrdinary = ordinaryToPhaseQuotient
    ; fromAfterTo = ordinaryPhaseRoundTrip
    ; toAfterFrom = phaseOrdinaryRoundTrip
    }

record PhaseQuotientJCoarseBoundary : Set where
  field
    exactCarrierEquivalenceConstructed : Bool
    exactCarrierEquivalenceConstructedIsTrue :
      exactCarrierEquivalenceConstructed ≡ true
    completionJIncludedInPhaseQuotient9 : Bool
    completionJIncludedInPhaseQuotient9IsFalse :
      completionJIncludedInPhaseQuotient9 ≡ false
    carrierEquivalenceClaimsGroupIsomorphism : Bool
    carrierEquivalenceClaimsGroupIsomorphismIsFalse :
      carrierEquivalenceClaimsGroupIsomorphism ≡ false

canonicalPhaseQuotientJCoarseBoundary :
  PhaseQuotientJCoarseBoundary
canonicalPhaseQuotientJCoarseBoundary =
  record
    { exactCarrierEquivalenceConstructed = true
    ; exactCarrierEquivalenceConstructedIsTrue = refl
    ; completionJIncludedInPhaseQuotient9 = false
    ; completionJIncludedInPhaseQuotient9IsFalse = refl
    ; carrierEquivalenceClaimsGroupIsomorphism = false
    ; carrierEquivalenceClaimsGroupIsomorphismIsFalse = refl
    }
