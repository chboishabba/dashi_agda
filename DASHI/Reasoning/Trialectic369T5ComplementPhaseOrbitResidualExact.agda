module DASHI.Reasoning.Trialectic369T5ComplementPhaseOrbitResidualExact where

------------------------------------------------------------------------
-- FIVE-TRIT COMPLEMENT -> K3 x FIVE-ORBIT QUOTIENT
--
-- DASHI CONTRIBUTION
--
-- Reuse the canonical kernel theorem:
--
--   K_(d+2) <-> K_d x T^2.
--
-- At d=3:
--
--   K5 <-> K3 x T^2
--      -> K3 x (T^2 / +/-)
--      = K3 x NineOrbit.
--
-- This quotient has 27*5 = 135 states, NOT 15.  Splitting K3 once more gives
--
--   K3 <-> K1 x T^2,
--
-- so the quotient target is structurally
--
--   K1 x T^2 x NineOrbit
--   = 3 x 9 x 5.
--
-- Thus an SSP-style 3x5 factor is present only together with an extra
-- nine-state residual.  No projection eliminating that residual is licensed
-- here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.Trialectic369DyadicLocalComplementFactorizationExact as Local
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction

------------------------------------------------------------------------
-- 1. Adapter from the literal AB five-trit complement to canonical K5.
------------------------------------------------------------------------

Kernel5 : Set
Kernel5 = Triadic.Kernel 5

Kernel3 : Set
Kernel3 = Triadic.Kernel 3

Kernel1 : Set
Kernel1 = Triadic.Kernel 1

abComplementToKernel5 :
  Local.ABComplement5 ->
  Kernel5
abComplementToKernel5 complement =
  Reduction.sspToKernelTrit (Local.ac complement) vcons
  Reduction.sspToKernelTrit (Local.bc complement) vcons
  Reduction.sspToKernelTrit (Local.ca complement) vcons
  Reduction.sspToKernelTrit (Local.cb complement) vcons
  Reduction.sspToKernelTrit (Local.cc complement) vcons
  vnil

kernel5ToABComplement :
  Kernel5 ->
  Local.ABComplement5
kernel5ToABComplement
  (ac vcons bc vcons ca vcons cb vcons cc vcons vnil) =
  Local.ab-complement5
    (Reduction.kernelToSSPTrit ac)
    (Reduction.kernelToSSPTrit bc)
    (Reduction.kernelToSSPTrit ca)
    (Reduction.kernelToSSPTrit cb)
    (Reduction.kernelToSSPTrit cc)

abComplementKernel5RoundTrip :
  (complement : Local.ABComplement5) ->
  kernel5ToABComplement (abComplementToKernel5 complement)
  ≡ complement
abComplementKernel5RoundTrip
  (Local.ab-complement5 ac bc ca cb cc)
  rewrite Reduction.sspKernelRoundTrip ac
        | Reduction.sspKernelRoundTrip bc
        | Reduction.sspKernelRoundTrip ca
        | Reduction.sspKernelRoundTrip cb
        | Reduction.sspKernelRoundTrip cc = refl

kernel5ABComplementRoundTrip :
  (kernel : Kernel5) ->
  abComplementToKernel5 (kernel5ToABComplement kernel)
  ≡ kernel
kernel5ABComplementRoundTrip
  (ac vcons bc vcons ca vcons cb vcons cc vcons vnil)
  rewrite Reduction.kernelSSPRoundTrip ac
        | Reduction.kernelSSPRoundTrip bc
        | Reduction.kernelSSPRoundTrip ca
        | Reduction.kernelSSPRoundTrip cb
        | Reduction.kernelSSPRoundTrip cc = refl

------------------------------------------------------------------------
-- 2. Canonical K5 -> K3 x NineOrbit quotient.
------------------------------------------------------------------------

record K3FiveOrbit : Set where
  constructor k3-five-orbit
  field
    residualK3 : Kernel3
    fiveOrbit : Triadic.NineOrbit

open K3FiveOrbit public

quotientKernel5 :
  Kernel5 ->
  K3FiveOrbit
quotientKernel5 kernel =
  let split = Triadic.splitNine kernel
  in
  k3-five-orbit
    (proj₁ split)
    (Triadic.quotientNine (proj₂ split))

canonicalLiftK3FiveOrbit :
  K3FiveOrbit ->
  Kernel5
canonicalLiftK3FiveOrbit state =
  Triadic.liftNine
    (residualK3 state)
    (Triadic.canonicalNineRepresentative (fiveOrbit state))

quotientCanonicalLift :
  (state : K3FiveOrbit) ->
  quotientKernel5 (canonicalLiftK3FiveOrbit state)
  ≡ state
quotientCanonicalLift (k3-five-orbit residual orbit)
  rewrite Triadic.splitLiftNine
            residual
            (Triadic.canonicalNineRepresentative orbit)
        | Triadic.canonicalRepresentativeReturnsOrbit orbit = refl

------------------------------------------------------------------------
-- 3. The quotient is invariant under inversion of the selected T2 sheet.
------------------------------------------------------------------------

invertSelectedSheet :
  Kernel5 ->
  Kernel5
invertSelectedSheet kernel =
  let split = Triadic.splitNine kernel
  in
  Triadic.liftNine
    (proj₁ split)
    (Triadic.negateNine (proj₂ split))

quotientSelectedSheetInversionInvariant :
  (kernel : Kernel5) ->
  quotientKernel5 (invertSelectedSheet kernel)
  ≡ quotientKernel5 kernel
quotientSelectedSheetInversionInvariant kernel
  with Triadic.splitNine kernel
... | residual , sheet
  rewrite Triadic.splitLiftNine residual (Triadic.negateNine sheet)
        | Triadic.quotientNineNegationInvariant sheet = refl

------------------------------------------------------------------------
-- 4. Split the residual K3 as K1 x T2.
------------------------------------------------------------------------

record K1NineFive : Set where
  constructor k1-nine-five
  field
    residualK1 : Kernel1
    residualNineSheet : Triadic.NineSheet
    orbitFive : Triadic.NineOrbit

open K1NineFive public

k3FiveToK1NineFive :
  K3FiveOrbit ->
  K1NineFive
k3FiveToK1NineFive state =
  let split = Triadic.splitNine (residualK3 state)
  in
  k1-nine-five
    (proj₁ split)
    (proj₂ split)
    (fiveOrbit state)

k1NineFiveToK3Five :
  K1NineFive ->
  K3FiveOrbit
k1NineFiveToK3Five state =
  k3-five-orbit
    (Triadic.liftNine
      (residualK1 state)
      (residualNineSheet state))
    (orbitFive state)

k1NineFiveRoundTrip :
  (state : K1NineFive) ->
  k3FiveToK1NineFive (k1NineFiveToK3Five state)
  ≡ state
k1NineFiveRoundTrip (k1-nine-five k1 sheet orbit)
  rewrite Triadic.splitLiftNine k1 sheet = refl

k3FiveRoundTrip :
  (state : K3FiveOrbit) ->
  k1NineFiveToK3Five (k3FiveToK1NineFive state)
  ≡ state
k3FiveRoundTrip (k3-five-orbit k3 orbit)
  rewrite Triadic.liftSplitNine k3 = refl

------------------------------------------------------------------------
-- 5. Exact count ledger.
------------------------------------------------------------------------

kernel1StateCount : Nat
kernel1StateCount = 3

nineSheetStateCount : Nat
nineSheetStateCount = 9

fiveOrbitStateCount : Nat
fiveOrbitStateCount = 5

quotientTargetStateCount : Nat
quotientTargetStateCount =
  kernel1StateCount * nineSheetStateCount * fiveOrbitStateCount

quotientTargetStateCountIs135 :
  quotientTargetStateCount ≡ 135
quotientTargetStateCountIs135 = refl

sspStyleFactorStateCount : Nat
sspStyleFactorStateCount =
  kernel1StateCount * fiveOrbitStateCount

sspStyleFactorStateCountIs15 :
  sspStyleFactorStateCount ≡ 15
sspStyleFactorStateCountIs15 = refl

extraNineResidualStateCountIsNine :
  nineSheetStateCount ≡ 9
extraNineResidualStateCountIsNine = refl

------------------------------------------------------------------------
-- 6. Firewall.
------------------------------------------------------------------------

data FiveTritComplementEqualsThreeTimesFiveCarrier : Set where
data NineResidualCanBeDroppedCanonically : Set where
data T5QuotientCreatesOggArithmeticIdentity : Set where

fiveTritComplementNotCollapsedToThreeTimesFive :
  FiveTritComplementEqualsThreeTimesFiveCarrier -> ⊥
fiveTritComplementNotCollapsedToThreeTimesFive ()

nineResidualNotDroppedWithoutNewLaw :
  NineResidualCanBeDroppedCanonically -> ⊥
nineResidualNotDroppedWithoutNewLaw ()

t5QuotientDoesNotCreateOggArithmeticIdentity :
  T5QuotientCreatesOggArithmeticIdentity -> ⊥
t5QuotientDoesNotCreateOggArithmeticIdentity ()

record Trialectic369T5ComplementPhaseOrbitResidualBoundary : Set where
  constructor trialectic-369-t5-complement-phase-orbit-residual-boundary
  field
    literalComplementToKernel5BidiPaid : Bool
    kernel5SplitsAsKernel3TimesT2 : Bool
    selectedT2InversionQuotientPaid : Bool
    quotientCanonicalSectionPaid : Bool
    quotientTargetIsKernel3TimesFiveOrbit : Bool
    kernel3SplitsAsKernel1TimesNineSheet : Bool
    quotientTargetCount135 : Bool
    sspStyleThreeTimesFiveFactorVisible : Bool
    extraNineStateResidualRetained : Bool
    complementCollapsedToSSP15Carrier : Bool

canonicalTrialectic369T5ComplementPhaseOrbitResidualBoundary :
  Trialectic369T5ComplementPhaseOrbitResidualBoundary
canonicalTrialectic369T5ComplementPhaseOrbitResidualBoundary =
  trialectic-369-t5-complement-phase-orbit-residual-boundary
    true true true true true true true true true false
