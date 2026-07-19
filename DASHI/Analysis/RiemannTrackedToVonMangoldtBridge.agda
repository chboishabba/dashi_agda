module DASHI.Analysis.RiemannTrackedToVonMangoldtBridge where

-- Termwise bridge from DASHI's finite tracked-prime arithmetic to the exact
-- all-prime von Mangoldt specification.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.TrackedPrimes using (SSP)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannPrimePowerArithmetic
open import DASHI.Analysis.RiemannVonMangoldtSpecification

cong₂ :
  {A B C : Set} →
  (op : A → B → C) →
  {x x′ : A} →
  {y y′ : B} →
  x ≡ x′ →
  y ≡ y′ →
  op x y ≡ op x′ y′
cong₂ op refl refl = refl

record TrackedPrimeVonMangoldtEmbedding
  (space : WeilTestSpace)
  (kernel : PrimePowerKernel space)
  (arithmetic : AllPrimeArithmetic space) : Set₁ where
  open WeilTestSpace space
  field
    includePrime : SSP → AllPrimeArithmetic.Prime arithmetic

    primePowerValueAgreement :
      (p : SSP) →
      (exponentIndex : Nat) →
      trackedPrimePowerValue p exponentIndex
      ≡
      primePowerNat space arithmetic (includePrime p) exponentIndex

    logWeightAgreement :
      (p : SSP) →
      PrimePowerKernel.logPrimeWeight kernel p
      ≡
      AllPrimeArithmetic.logPrimeWeight arithmetic (includePrime p)

    sampleAgreement :
      (f : Test) →
      (n : Nat) →
      PrimePowerKernel.sampleAtNat kernel f n
      ≡
      AllPrimeArithmetic.sampleAtNat arithmetic f n

    multiplicationAgreement :
      (x y : Scalar) →
      PrimePowerKernel._*S_ kernel x y
      ≡
      AllPrimeArithmetic._*S_ arithmetic x y

lambdaAtTrackedPrimePower :
  (space : WeilTestSpace) →
  (kernel : PrimePowerKernel space) →
  (arithmetic : AllPrimeArithmetic space) →
  (mangoldt : VonMangoldtFunction space arithmetic) →
  (embedding :
    TrackedPrimeVonMangoldtEmbedding space kernel arithmetic) →
  (p : SSP) →
  (exponentIndex : Nat) →
  VonMangoldtFunction.lambda mangoldt
    (trackedPrimePowerValue p exponentIndex)
  ≡
  AllPrimeArithmetic.logPrimeWeight arithmetic
    (TrackedPrimeVonMangoldtEmbedding.includePrime embedding p)
lambdaAtTrackedPrimePower
  space kernel arithmetic mangoldt embedding p exponentIndex =
  VonMangoldtFunction.specificationSingleValued mangoldt
    (trackedPrimePowerValue p exponentIndex)
    (VonMangoldtFunction.lambda mangoldt
      (trackedPrimePowerValue p exponentIndex))
    (AllPrimeArithmetic.logPrimeWeight arithmetic
      (TrackedPrimeVonMangoldtEmbedding.includePrime embedding p))
    (VonMangoldtFunction.lambdaSpecified mangoldt
      (trackedPrimePowerValue p exponentIndex))
    (atPrimePower
      (TrackedPrimeVonMangoldtEmbedding.includePrime embedding p)
      exponentIndex
      (TrackedPrimeVonMangoldtEmbedding.primePowerValueAgreement
        embedding p exponentIndex))

trackedPrimePowerTermAgreesWithVonMangoldt :
  (space : WeilTestSpace) →
  (kernel : PrimePowerKernel space) →
  (arithmetic : AllPrimeArithmetic space) →
  (mangoldt : VonMangoldtFunction space arithmetic) →
  (embedding :
    TrackedPrimeVonMangoldtEmbedding space kernel arithmetic) →
  (f : WeilTestSpace.Test space) →
  (p : SSP) →
  (exponentIndex : Nat) →
  weightedPrimePowerTerm space kernel f p exponentIndex
  ≡
  vonMangoldtSampleTerm space arithmetic mangoldt f
    (trackedPrimePowerValue p exponentIndex)
trackedPrimePowerTermAgreesWithVonMangoldt
  space kernel arithmetic mangoldt embedding f p exponentIndex =
  ≡-trans
    (TrackedPrimeVonMangoldtEmbedding.multiplicationAgreement embedding
      (PrimePowerKernel.logPrimeWeight kernel p)
      (PrimePowerKernel.sampleAtNat kernel f
        (trackedPrimePowerValue p exponentIndex)))
    (≡-trans
      (cong₂
        (AllPrimeArithmetic._*S_ arithmetic)
        (TrackedPrimeVonMangoldtEmbedding.logWeightAgreement embedding p)
        (TrackedPrimeVonMangoldtEmbedding.sampleAgreement embedding f
          (trackedPrimePowerValue p exponentIndex)))
      (cong₂
        (AllPrimeArithmetic._*S_ arithmetic)
        (≡-sym
          (lambdaAtTrackedPrimePower
            space kernel arithmetic mangoldt embedding p exponentIndex))
        refl))
