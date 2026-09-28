module DASHI.Reasoning.Trialectic369DyadicLocalComplementFactorizationExact where

------------------------------------------------------------------------
-- GLOBAL T9 <-> DYADIC LOCAL T4 x COMPLEMENT T5
--
-- DASHI CONTRIBUTION
--
-- For the AB local chart:
--
--   local      = (AA, AB, BA, BB)             -- 4 trits
--   complement = (AC, BC, CA, CB, CC)         -- 5 trits
--
-- so the global 3x3 observer matrix admits an exact two-sided rechart
--
--   ObserverMatrix3 SSPTrit <-> ABSection x Kernel 5.
--
-- The same construction is available cyclically for BC and CA.
--
-- This gives a pre-RH geometric interpretation of the depth-five factor:
-- it is the literal five-trit complement to a chosen dyadic local chart.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.Trialectic369DescentNaturalityExact as Descent
import DASHI.Reasoning.Trialectic369DyadicSectionTriadicKernelExact as Dyadic

open Codec using ([]ᵥ; _∷ᵥ_)

Kernel5 : Set
Kernel5 = Codec.Kernel 5

------------------------------------------------------------------------
-- 1. AB complement and exact global rechart.
------------------------------------------------------------------------

record ABComplement5 : Set where
  constructor ab-complement5
  field
    ac : SSP.SSPTrit
    bc : SSP.SSPTrit
    ca : SSP.SSPTrit
    cb : SSP.SSPTrit
    cc : SSP.SSPTrit

open ABComplement5 public

observerABComplement :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  ABComplement5
observerABComplement matrix =
  ab-complement5
    (Observer.aC matrix)
    (Observer.bC matrix)
    (Observer.cA matrix)
    (Observer.cB matrix)
    (Observer.cC matrix)

record ABLocalComplementPoint : Set where
  constructor ab-local-complement-point
  field
    localAB : Descent.ABSection
    complementAB : ABComplement5

open ABLocalComplementPoint public

observerToABLocalComplement :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  ABLocalComplementPoint
observerToABLocalComplement matrix =
  ab-local-complement-point
    (Descent.restrictAB matrix)
    (observerABComplement matrix)

abLocalComplementToObserver :
  ABLocalComplementPoint ->
  Observer.ObserverMatrix3 SSP.SSPTrit
abLocalComplementToObserver
  (ab-local-complement-point
    (Descent.ab-section aa ab ba bb)
    (ab-complement5 ac bc ca cb cc)) =
  Observer.observerMatrix3
    aa ab ac
    ba bb bc
    ca cb cc

observerABLocalComplementRoundTrip :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  abLocalComplementToObserver
    (observerToABLocalComplement matrix)
  ≡ matrix
observerABLocalComplementRoundTrip
  (Observer.observerMatrix3
    aa ab ac ba bb bc ca cb cc) = refl

abLocalComplementObserverRoundTrip :
  (state : ABLocalComplementPoint) ->
  observerToABLocalComplement
    (abLocalComplementToObserver state)
  ≡ state
abLocalComplementObserverRoundTrip
  (ab-local-complement-point
    (Descent.ab-section aa ab ba bb)
    (ab-complement5 ac bc ca cb cc)) = refl

------------------------------------------------------------------------
-- 2. The complement is exactly canonical Kernel 5.
------------------------------------------------------------------------

abComplementToKernel5 : ABComplement5 -> Kernel5
abComplementToKernel5 complement =
  SSP.toTrit (ac complement) ∷ᵥ
  SSP.toTrit (bc complement) ∷ᵥ
  SSP.toTrit (ca complement) ∷ᵥ
  SSP.toTrit (cb complement) ∷ᵥ
  SSP.toTrit (cc complement) ∷ᵥ
  []ᵥ

kernel5ToABComplement : Kernel5 -> ABComplement5
kernel5ToABComplement
  (acT ∷ᵥ bcT ∷ᵥ caT ∷ᵥ cbT ∷ᵥ ccT ∷ᵥ []ᵥ) =
  ab-complement5
    (SSP.fromTrit acT)
    (SSP.fromTrit bcT)
    (SSP.fromTrit caT)
    (SSP.fromTrit cbT)
    (SSP.fromTrit ccT)

abComplementKernel5RoundTrip :
  (complement : ABComplement5) ->
  kernel5ToABComplement (abComplementToKernel5 complement)
  ≡ complement
abComplementKernel5RoundTrip
  (ab-complement5 acv bcv cav cbv ccv)
  rewrite SSP.fromTrit-toTrit acv
        | SSP.fromTrit-toTrit bcv
        | SSP.fromTrit-toTrit cav
        | SSP.fromTrit-toTrit cbv
        | SSP.fromTrit-toTrit ccv = refl

kernel5ABComplementRoundTrip :
  (kernel : Kernel5) ->
  abComplementToKernel5 (kernel5ToABComplement kernel)
  ≡ kernel
kernel5ABComplementRoundTrip
  (acT ∷ᵥ bcT ∷ᵥ caT ∷ᵥ cbT ∷ᵥ ccT ∷ᵥ []ᵥ)
  rewrite SSP.toTrit-fromTrit acT
        | SSP.toTrit-fromTrit bcT
        | SSP.toTrit-fromTrit caT
        | SSP.toTrit-fromTrit cbT
        | SSP.toTrit-fromTrit ccT = refl

------------------------------------------------------------------------
-- 3. Combined canonical Kernel 4 x Kernel 5 chart.
------------------------------------------------------------------------

record Kernel4xKernel5 : Set where
  constructor kernel4xkernel5
  field
    localKernel4 : Dyadic.KernelBridge.Kernel4
    complementKernel5 : Kernel5

open Kernel4xKernel5 public

observerToKernel4xKernel5 :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Kernel4xKernel5
observerToKernel4xKernel5 matrix =
  kernel4xkernel5
    (Dyadic.abToKernel4 (Descent.restrictAB matrix))
    (abComplementToKernel5 (observerABComplement matrix))

kernel4xKernel5ToObserver :
  Kernel4xKernel5 ->
  Observer.ObserverMatrix3 SSP.SSPTrit
kernel4xKernel5ToObserver
  (kernel4xkernel5 local complement) =
  abLocalComplementToObserver
    (ab-local-complement-point
      (Dyadic.kernel4ToAB local)
      (kernel5ToABComplement complement))

observerKernel4xKernel5RoundTrip :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  kernel4xKernel5ToObserver
    (observerToKernel4xKernel5 matrix)
  ≡ matrix
observerKernel4xKernel5RoundTrip matrix
  rewrite Dyadic.abKernelRoundTrip (Descent.restrictAB matrix)
        | abComplementKernel5RoundTrip (observerABComplement matrix) =
  observerABLocalComplementRoundTrip matrix

kernel4xKernel5ObserverRoundTrip :
  (state : Kernel4xKernel5) ->
  observerToKernel4xKernel5
    (kernel4xKernel5ToObserver state)
  ≡ state
kernel4xKernel5ObserverRoundTrip
  (kernel4xkernel5 local complement)
  rewrite Dyadic.kernelABRoundTrip local
        | kernel5ABComplementRoundTrip complement = refl

------------------------------------------------------------------------
-- 4. Cardinal arithmetic.
------------------------------------------------------------------------

localKernel4StateCount : Nat
localKernel4StateCount = 81

complementKernel5StateCount : Nat
complementKernel5StateCount = 243

globalKernel9StateCount : Nat
globalKernel9StateCount = 19683

globalFactorizationCount :
  globalKernel9StateCount
  ≡ localKernel4StateCount * complementKernel5StateCount
globalFactorizationCount = refl

------------------------------------------------------------------------
-- 5. Firewall.
------------------------------------------------------------------------

data FiveTritComplementCreatesRHDepthMechanism : Set where
data ChosenABComplementIsIntrinsicPreferredChart : Set where

fiveTritComplementDoesNotCreateRHMechanism :
  FiveTritComplementCreatesRHDepthMechanism -> ⊥
fiveTritComplementDoesNotCreateRHMechanism ()

abChartNotPromotedToIntrinsicPreference :
  ChosenABComplementIsIntrinsicPreferredChart -> ⊥
abChartNotPromotedToIntrinsicPreference ()

record Trialectic369DyadicLocalComplementFactorizationBoundary : Set where
  constructor trialectic-369-dyadic-local-complement-factorization-boundary
  field
    globalObserverToABLocalComplementExact : Bool
    abLocalIsCanonicalKernel4 : Bool
    abComplementIsCanonicalKernel5 : Bool
    globalObserverIsKernel4TimesKernel5 : Bool
    count81Times243Equals19683 : Bool
    rhDepthMechanismClaimed : Bool
    abChartClaimedIntrinsicPreferred : Bool

canonicalTrialectic369DyadicLocalComplementFactorizationBoundary :
  Trialectic369DyadicLocalComplementFactorizationBoundary
canonicalTrialectic369DyadicLocalComplementFactorizationBoundary =
  trialectic-369-dyadic-local-complement-factorization-boundary
    true true true true true false false
