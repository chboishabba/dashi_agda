module DASHI.Arithmetic.SignedSSPTwinObservableTransportExact where

------------------------------------------------------------------------
-- SOURCE OWNERS / ATTRIBUTION
--
-- DASHI.Combinatorics.SSP15FractranCompression:
--   lossless (SSP label, residual) code; no assumed bare-label encoding.
-- DASHI.Combinatorics.FractranComputationEquivalence:
--   SameOutcome means identical terminal FRACTRAN results, not equal
--   trace/program, and requires source/target simulation separately.
-- DASHI.Combinatorics.FractranCOL:
--   concrete finite exponent-vector FRACTRAN evaluator.
-- DASHI.Arithmetic.TwinPrimeCertifiedEnumeratorExact:
--   proof-bearing arithmetic pair predicate and exact indicator/count.
--
-- NEW transport: a lossless SSP label+residual can carry every
-- arithmetic twin predicate and its exact finite count observable.
-- Also, two FRACTRAN states with the same terminal result necessarily
-- agree on any twin-primality observable of that terminal state.
--
-- These theorems are CONDITIONAL on a genuine lossless codec, or on
-- a SameOutcome proof. They do not construct a universal SSP15 codec,
-- a generic FRACTRAN compiler, or a prime distribution theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
import DASHI.Combinatorics.FractranCOL as FRACTRAN
import DASHI.Combinatorics.FractranComputationEquivalence as Equiv
import DASHI.Combinatorics.SSP15FractranCompression as Compression
import DASHI.Arithmetic.TwinPrimeCertifiedEnumeratorExact as TwinCount
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin

-- A proven lossless SSP15 codec preserves the original arithmetic
-- readout of the exact FRACTRAN exponent-vector state.
losslessSSPReadoutRoundTrip :
  (C : Compression.SSP15ResidualCodec) →
  (readout : FRACTRAN.EV5 → Nat) →
  (state : FRACTRAN.EV5) →
  readout (Compression.decodeState C (Compression.encodeState C state))
    ≡ readout state
losslessSSPReadoutRoundTrip C readout state =
  cong readout (Compression.codec-roundtrip C state)

losslessSSPPreservesActualTwinPredicate :
  (C : Compression.SSP15ResidualCodec) →
  (readout : FRACTRAN.EV5 → Nat) →
  (state : FRACTRAN.EV5) →
  Twin.TwinPrimeAt (readout state) →
  Twin.TwinPrimeAt
    (readout (Compression.decodeState C (Compression.encodeState C state)))
losslessSSPPreservesActualTwinPredicate C readout state = 
  subst Twin.TwinPrimeAt
    (sym (losslessSSPReadoutRoundTrip C readout state))

losslessSSPPreservesExactTwinIndicator :
  (C : Compression.SSP15ResidualCodec) →
  (readout : FRACTRAN.EV5 → Nat) →
  (state : FRACTRAN.EV5) →
  TwinCount.twinPairIndicator
    (readout (Compression.decodeState C (Compression.encodeState C state)))
  ≡ TwinCount.twinPairIndicator (readout state)
losslessSSPPreservesExactTwinIndicator C readout state =
  cong TwinCount.twinPairIndicator
    (losslessSSPReadoutRoundTrip C readout state)

-- SameOutcome is weaker than trace equivalence, but suffices to
-- preserve ANY deterministic terminal Nat twin-pair observation.
terminalSameOutcomeTwinIndicator :
  (readout : FRACTRAN.EV5 → Nat) →
  (left right : FRACTRAN.EV5) →
  Equiv.SameOutcome left right →
  TwinCount.twinPairIndicator (readout (FRACTRAN.run left))
  ≡ TwinCount.twinPairIndicator (readout (FRACTRAN.run right))
terminalSameOutcomeTwinIndicator readout left right same =
  cong (λ state → TwinCount.twinPairIndicator (readout state)) same

terminalSameOutcomeTwinPrimeProof :
  (readout : FRACTRAN.EV5 → Nat) →
  (left right : FRACTRAN.EV5) →
  Equiv.SameOutcome left right →
  Twin.TwinPrimeAt (readout (FRACTRAN.run left)) →
  Twin.TwinPrimeAt (readout (FRACTRAN.run right))
terminalSameOutcomeTwinPrimeProof readout left right same =
  subst (λ state → Twin.TwinPrimeAt (readout state)) same
