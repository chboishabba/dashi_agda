module DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- The C3 phase quotient Q9 = T x T and the existing NonaryTruth ring both
-- have nine elements, but they carry different group structures:
--
--   Q9  ~ C3 x C3          (exponent 3)
--   NonaryTruth ~ C9       (contains an element of order 9).
--
-- This module does two things.
--
-- 1. It constructs an explicit two-sided row-major carrier chart Q9 <->
--    NonaryTruth.
-- 2. It proves that NO group isomorphism can preserve the componentwise
--    triXor law on Q9 and the cyclic nonaryXor law on NonaryTruth.
--
-- Thus an Aristotle/base-9 residue presentation can be used as an address
-- chart without silently identifying its algebra with the phase quotient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Base369 as Base
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase

phasePairToNonary :
  Phase.PhaseQuotient9 → Base.NonaryTruth
phasePairToNonary (Base.tri-low , Base.tri-low) = Base.non-0
phasePairToNonary (Base.tri-low , Base.tri-mid) = Base.non-1
phasePairToNonary (Base.tri-low , Base.tri-high) = Base.non-2
phasePairToNonary (Base.tri-mid , Base.tri-low) = Base.non-3
phasePairToNonary (Base.tri-mid , Base.tri-mid) = Base.non-4
phasePairToNonary (Base.tri-mid , Base.tri-high) = Base.non-5
phasePairToNonary (Base.tri-high , Base.tri-low) = Base.non-6
phasePairToNonary (Base.tri-high , Base.tri-mid) = Base.non-7
phasePairToNonary (Base.tri-high , Base.tri-high) = Base.non-8

nonaryToPhasePair :
  Base.NonaryTruth → Phase.PhaseQuotient9
nonaryToPhasePair Base.non-0 = Base.tri-low , Base.tri-low
nonaryToPhasePair Base.non-1 = Base.tri-low , Base.tri-mid
nonaryToPhasePair Base.non-2 = Base.tri-low , Base.tri-high
nonaryToPhasePair Base.non-3 = Base.tri-mid , Base.tri-low
nonaryToPhasePair Base.non-4 = Base.tri-mid , Base.tri-mid
nonaryToPhasePair Base.non-5 = Base.tri-mid , Base.tri-high
nonaryToPhasePair Base.non-6 = Base.tri-high , Base.tri-low
nonaryToPhasePair Base.non-7 = Base.tri-high , Base.tri-mid
nonaryToPhasePair Base.non-8 = Base.tri-high , Base.tri-high

phaseNonaryRoundTrip :
  (pair : Phase.PhaseQuotient9) →
  nonaryToPhasePair (phasePairToNonary pair) ≡ pair
phaseNonaryRoundTrip (Base.tri-low , Base.tri-low) = refl
phaseNonaryRoundTrip (Base.tri-low , Base.tri-mid) = refl
phaseNonaryRoundTrip (Base.tri-low , Base.tri-high) = refl
phaseNonaryRoundTrip (Base.tri-mid , Base.tri-low) = refl
phaseNonaryRoundTrip (Base.tri-mid , Base.tri-mid) = refl
phaseNonaryRoundTrip (Base.tri-mid , Base.tri-high) = refl
phaseNonaryRoundTrip (Base.tri-high , Base.tri-low) = refl
phaseNonaryRoundTrip (Base.tri-high , Base.tri-mid) = refl
phaseNonaryRoundTrip (Base.tri-high , Base.tri-high) = refl

nonaryPhaseRoundTrip :
  (value : Base.NonaryTruth) →
  phasePairToNonary (nonaryToPhasePair value) ≡ value
nonaryPhaseRoundTrip Base.non-0 = refl
nonaryPhaseRoundTrip Base.non-1 = refl
nonaryPhaseRoundTrip Base.non-2 = refl
nonaryPhaseRoundTrip Base.non-3 = refl
nonaryPhaseRoundTrip Base.non-4 = refl
nonaryPhaseRoundTrip Base.non-5 = refl
nonaryPhaseRoundTrip Base.non-6 = refl
nonaryPhaseRoundTrip Base.non-7 = refl
nonaryPhaseRoundTrip Base.non-8 = refl

q9Add :
  Phase.PhaseQuotient9 →
  Phase.PhaseQuotient9 →
  Phase.PhaseQuotient9
q9Add (a0 , a1) (b0 , b1) =
  Base.triXor a0 b0 , Base.triXor a1 b1

q9Zero : Phase.PhaseQuotient9
q9Zero = Base.tri-low , Base.tri-low

q9TripleIsZero :
  (pair : Phase.PhaseQuotient9) →
  q9Add (q9Add pair pair) pair ≡ q9Zero
q9TripleIsZero (Base.tri-low , Base.tri-low) = refl
q9TripleIsZero (Base.tri-low , Base.tri-mid) = refl
q9TripleIsZero (Base.tri-low , Base.tri-high) = refl
q9TripleIsZero (Base.tri-mid , Base.tri-low) = refl
q9TripleIsZero (Base.tri-mid , Base.tri-mid) = refl
q9TripleIsZero (Base.tri-mid , Base.tri-high) = refl
q9TripleIsZero (Base.tri-high , Base.tri-low) = refl
q9TripleIsZero (Base.tri-high , Base.tri-mid) = refl
q9TripleIsZero (Base.tri-high , Base.tri-high) = refl

naturalChartDoesNotPreserveAddition :
  phasePairToNonary
    (q9Add
      (Base.tri-low , Base.tri-mid)
      (Base.tri-low , Base.tri-high))
  ≡
  Base.nonaryXor
    (phasePairToNonary (Base.tri-low , Base.tri-mid))
    (phasePairToNonary (Base.tri-low , Base.tri-high))
  →
  ⊥
naturalChartDoesNotPreserveAddition ()

nonaryIdempotentIsZero :
  (value : Base.NonaryTruth) →
  Base.nonaryXor value value ≡ value →
  value ≡ Base.non-0
nonaryIdempotentIsZero Base.non-0 equality = refl
nonaryIdempotentIsZero Base.non-1 ()
nonaryIdempotentIsZero Base.non-2 ()
nonaryIdempotentIsZero Base.non-3 ()
nonaryIdempotentIsZero Base.non-4 ()
nonaryIdempotentIsZero Base.non-5 ()
nonaryIdempotentIsZero Base.non-6 ()
nonaryIdempotentIsZero Base.non-7 ()
nonaryIdempotentIsZero Base.non-8 ()

record Q9NonaryGroupIsomorphism : Set where
  field
    encode : Phase.PhaseQuotient9 → Base.NonaryTruth
    decode : Base.NonaryTruth → Phase.PhaseQuotient9
    decodeEncode :
      (pair : Phase.PhaseQuotient9) →
      decode (encode pair) ≡ pair
    encodeDecode :
      (value : Base.NonaryTruth) →
      encode (decode value) ≡ value
    preserveAddition :
      (left right : Phase.PhaseQuotient9) →
      encode (q9Add left right)
      ≡ Base.nonaryXor (encode left) (encode right)

open Q9NonaryGroupIsomorphism public

encodeZeroIsNonaryZero :
  (iso : Q9NonaryGroupIsomorphism) →
  encode iso q9Zero ≡ Base.non-0
encodeZeroIsNonaryZero iso =
  nonaryIdempotentIsZero
    (encode iso q9Zero)
    (sym (preserveAddition iso q9Zero q9Zero))

tripleNonaryOneIsThree :
  Base.nonaryXor
    (Base.nonaryXor Base.non-1 Base.non-1)
    Base.non-1
  ≡ Base.non-3
tripleNonaryOneIsThree = refl

nonaryZeroIsNotThree : Base.non-0 ≡ Base.non-3 → ⊥
nonaryZeroIsNotThree ()

q9NonaryGroupIsomorphismImpossible :
  Q9NonaryGroupIsomorphism → ⊥
q9NonaryGroupIsomorphismImpossible iso =
  nonaryZeroIsNotThree contradiction
  where
  x : Phase.PhaseQuotient9
  x = decode iso Base.non-1

  tripleTransport :
    encode iso (q9Add (q9Add x x) x)
    ≡
    Base.nonaryXor
      (Base.nonaryXor (encode iso x) (encode iso x))
      (encode iso x)
  tripleTransport =
    trans
      (preserveAddition iso (q9Add x x) x)
      (cong
        (λ value →
          Base.nonaryXor value (encode iso x))
        (preserveAddition iso x x))

  tripleImageIsThree :
    Base.nonaryXor
      (Base.nonaryXor (encode iso x) (encode iso x))
      (encode iso x)
    ≡ Base.non-3
  tripleImageIsThree
    rewrite encodeDecode iso Base.non-1 =
    tripleNonaryOneIsThree

  contradiction : Base.non-0 ≡ Base.non-3
  contradiction =
    trans
      (sym (encodeZeroIsNonaryZero iso))
      (trans
        (sym (cong (encode iso) (q9TripleIsZero x)))
        (trans tripleTransport tripleImageIsThree))

record PhaseQuotientNonaryBoundary : Set where
  field
    exactNineStateCarrierChartConstructed : Bool
    exactNineStateCarrierChartConstructedIsTrue :
      exactNineStateCarrierChartConstructed ≡ true
    naturalChartPreservesGroupLaw : Bool
    naturalChartPreservesGroupLawIsFalse :
      naturalChartPreservesGroupLaw ≡ false
    anyGroupIsomorphismExists : Bool
    anyGroupIsomorphismExistsIsFalse :
      anyGroupIsomorphismExists ≡ false

canonicalPhaseQuotientNonaryBoundary :
  PhaseQuotientNonaryBoundary
canonicalPhaseQuotientNonaryBoundary =
  record
    { exactNineStateCarrierChartConstructed = true
    ; exactNineStateCarrierChartConstructedIsTrue = refl
    ; naturalChartPreservesGroupLaw = false
    ; naturalChartPreservesGroupLawIsFalse = refl
    ; anyGroupIsomorphismExists = false
    ; anyGroupIsomorphismExistsIsFalse = refl
    }
