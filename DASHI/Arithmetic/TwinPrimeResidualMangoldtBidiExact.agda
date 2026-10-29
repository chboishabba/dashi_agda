module DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact where

------------------------------------------------------------------------
-- CONSUMER-SAFE RESIDUAL / MANGOLDT BIDI
--
-- REUSE OWNERS, DO NOT REDEFINE:
-- DASHI.Cognition.ResidualPhaseGeometry: Projection, Fibre/Residual
-- DASHI.Core.ConsumerGuidedReopenableRefinementExact:
--   exact consumer-sufficient vs consumer-collision boundary
-- DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact:
--   both Nat <-> (period, Fin270) inverse proofs
-- DASHI.Analysis.RiemannVonMangoldtSpecification:
--   original von Mangoldt relational prime-power specification.
--
-- This transports ANY number-theoretic consumer, including the
-- original von Mangoldt scalar function, with exact pointwise equality.
-- It does NOT prove a positive prime-pair correlation estimate.
-- Source written; Agda kernel pending. 2026-10-29.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Cognition.ResidualPhaseGeometry as Phase
import DASHI.Core.ConsumerGuidedReopenableRefinementExact as Refine
import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM

-- Existing residual-carrier construction: not a duplicate Sigma
-- representation invented alongside ResidualPhaseGeometry.
periodProjection : Phase.Projection Nat Period.NatPeriod270
periodProjection = record { observe = Period.encodeNatPeriod270 }

exactPeriodResidual :
  (code : Period.NatPeriod270) → Set
exactPeriodResidual = Phase.Residual periodProjection

-- The actual residual witness is an original Nat, together with
-- the exact proof of its encoded observed state.
natGivesPeriodResidual :
  (n : Nat) →
  exactPeriodResidual (Period.encodeNatPeriod270 n)
natGivesPeriodResidual n = n , refl

-- Every witnessed residual fibre is a SINGLE concrete Nat;
-- this follows from the inverse law, not a boolean receipt.
periodResidualUniqueness :
  (code : Period.NatPeriod270) →
  (witness : exactPeriodResidual code) →
  proj₁ witness ≡ Period.decodeNatPeriod270 code
periodResidualUniqueness code (n , proof) =
  trans
    (sym (Period.decodeEncodeNatPeriod270 n))
    (cong Period.decodeNatPeriod270 proof)

-- Two-sided factorisation is exactly what the refinement kernel
-- demands of a consumer-safe representation. No arbitrary fibration
-- or quotient is assumed to preserve the consumer.
liftNatConsumer :
  {Output : Set} →
  (Nat → Output) → Period.NatPeriod270 → Output
liftNatConsumer consumer code =
  consumer (Period.decodeNatPeriod270 code)

liftConsumerSound :
  {Output : Set} (consumer : Nat → Output) (n : Nat) →
  liftNatConsumer consumer (Period.encodeNatPeriod270 n)
    ≡ consumer n
liftConsumerSound consumer n =
  cong consumer (Period.decodeEncodeNatPeriod270 n)

liftConsumerComplete :
  {Output : Set} (consumer : Nat → Output) →
  (code : Period.NatPeriod270) →
  consumer (Period.decodeNatPeriod270 code)
    ≡ liftNatConsumer consumer code
liftConsumerComplete consumer code = refl

periodConsumerBidi :
  {Output : Set} (consumer : Nat → Output) →
  ((n : Nat) →
    liftNatConsumer consumer (Period.encodeNatPeriod270 n)
      ≡ consumer n)
periodConsumerBidi = liftConsumerSound

-- Reuse the ORIGINAL Mangoldt specification. Its scalar carrier
-- is WeilTestSpace.Scalar space; do not coerce it into Nat or Float.
mangoldtAtPeriod :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  Period.NatPeriod270 → Weil.WeilTestSpace.Scalar space
mangoldtAtPeriod space arithmetic mangoldt =
  liftNatConsumer (VM.VonMangoldtFunction.lambda mangoldt)

mangoldtPeriodForward :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (n : Nat) →
  mangoldtAtPeriod space arithmetic mangoldt
    (Period.encodeNatPeriod270 n)
  ≡ VM.VonMangoldtFunction.lambda mangoldt n
mangoldtPeriodForward space arithmetic mangoldt =
  liftConsumerSound (VM.VonMangoldtFunction.lambda mangoldt)

mangoldtPeriodBackward :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (code : Period.NatPeriod270) →
  VM.VonMangoldtFunction.lambda mangoldt
    (Period.decodeNatPeriod270 code)
  ≡ mangoldtAtPeriod space arithmetic mangoldt code
mangoldtPeriodBackward space arithmetic mangoldt code = refl

-- Prime-pair correlations can be represented faithfully, but
-- positivity must come from a separate ANALYTIC theorem.
record ArithmeticPairCorrelation
  (Scalar : Set) : Set₁ where
  field
    lambdaWeight : Nat → Scalar
    multiply : Scalar → Scalar → Scalar
open ArithmeticPairCorrelation public

pairCorrelationAtNat :
  {Scalar : Set} →
  ArithmeticPairCorrelation Scalar → Nat → Scalar
pairCorrelationAtNat C n =
  multiply C (lambdaWeight C n) (lambdaWeight C (n + 2))

pairCorrelationAtPeriod :
  {Scalar : Set} →
  ArithmeticPairCorrelation Scalar →
  Period.NatPeriod270 → Scalar
pairCorrelationAtPeriod C =
  liftNatConsumer (pairCorrelationAtNat C)

pairCorrelationForward :
  {Scalar : Set} (C : ArithmeticPairCorrelation Scalar) (n : Nat) →
  pairCorrelationAtPeriod C (Period.encodeNatPeriod270 n)
    ≡ pairCorrelationAtNat C n
pairCorrelationForward C = liftConsumerSound (pairCorrelationAtNat C)

pairCorrelationBackward :
  {Scalar : Set} (C : ArithmeticPairCorrelation Scalar)
  (code : Period.NatPeriod270) →
  pairCorrelationAtNat C (Period.decodeNatPeriod270 code)
    ≡ pairCorrelationAtPeriod C code
pairCorrelationBackward C code = refl

-- Any claimed positive lower bound for this correlation is
-- deliberately ABSENT. This file establishes only faithful BIDI
-- transportation of the *same* numeric sequence.
