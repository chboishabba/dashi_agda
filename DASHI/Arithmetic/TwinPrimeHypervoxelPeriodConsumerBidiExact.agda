{-# OPTIONS --safe #-}
module DASHI.Arithmetic.TwinPrimeHypervoxelPeriodConsumerBidiExact where

-- Concrete arithmetic state BIDI, retaining the original integer history
-- and its separate cubie/hypervoxel refinement. Unlike a coarse-only
-- projection, the period codec is invertible and the fine address is kept.
-- No asymptotic arithmetic estimate is postulated.

open import DASHI.Core.Prelude
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper
import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period
import DASHI.Arithmetic.TwinPrimeActualPairSectionGluingExact as Pair
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM

record ArithmeticHistory (rank coarseDepth fineDepth : Nat) : Set where
  constructor arithmeticHistory
  field
    original : Nat
    coarse : Hyper.TernaryAddress rank coarseDepth
    suffix : Hyper.AddressSuffix rank fineDepth
open ArithmeticHistory public

record EncodedArithmeticHistory (rank coarseDepth fineDepth : Nat) : Set where
  constructor encodedArithmeticHistory
  field
    period : Period.NatPeriod270
    coarseCode : Hyper.TernaryAddress rank coarseDepth
    suffixCode : Hyper.AddressSuffix rank fineDepth
open EncodedArithmeticHistory public

encode : ∀ {rank coarseDepth fineDepth} →
  ArithmeticHistory rank coarseDepth fineDepth →
  EncodedArithmeticHistory rank coarseDepth fineDepth
encode h = encodedArithmeticHistory
  (Period.encodeNatPeriod270 (original h)) (coarse h) (suffix h)

decode : ∀ {rank coarseDepth fineDepth} →
  EncodedArithmeticHistory rank coarseDepth fineDepth →
  ArithmeticHistory rank coarseDepth fineDepth
decode h = arithmeticHistory
  (Period.decodeNatPeriod270 (period h)) (coarseCode h) (suffixCode h)

decodeEncode : ∀ {rank coarseDepth fineDepth} →
  (h : ArithmeticHistory rank coarseDepth fineDepth) →
  decode (encode h) ≡ h
decodeEncode (arithmeticHistory n c s)
  rewrite Period.decodeEncodeNatPeriod270 n = refl

encodeDecode : ∀ {rank coarseDepth fineDepth} →
  (h : EncodedArithmeticHistory rank coarseDepth fineDepth) →
  encode (decode h) ≡ h
encodeDecode (encodedArithmeticHistory n c s)
  rewrite Period.encodeDecodeNatPeriod270 n = refl

refinedAddress : ∀ {rank coarseDepth fineDepth} →
  ArithmeticHistory rank coarseDepth fineDepth →
  Hyper.TernaryAddress rank (Hyper._⊕_ coarseDepth fineDepth)
refinedAddress h = Hyper.joinAddress (coarse h) (suffix h)

encodedRefinedAddress : ∀ {rank coarseDepth fineDepth} →
  EncodedArithmeticHistory rank coarseDepth fineDepth →
  Hyper.TernaryAddress rank (Hyper._⊕_ coarseDepth fineDepth)
encodedRefinedAddress h = Hyper.joinAddress (coarseCode h) (suffixCode h)

finePreserved : ∀ {rank coarseDepth fineDepth} →
  (h : ArithmeticHistory rank coarseDepth fineDepth) →
  encodedRefinedAddress (encode h) ≡ refinedAddress h
finePreserved h = refl

consumerAtHistory : ∀ {rank coarseDepth fineDepth Output} →
  (Nat → Output) → ArithmeticHistory rank coarseDepth fineDepth → Output
consumerAtHistory f h = f (original h)

consumerAtCode : ∀ {rank coarseDepth fineDepth Output} →
  (Nat → Output) → EncodedArithmeticHistory rank coarseDepth fineDepth → Output
consumerAtCode f h = f (Period.decodeNatPeriod270 (period h))

consumerForward : ∀ {rank coarseDepth fineDepth Output} →
  (f : Nat → Output) →
  (h : ArithmeticHistory rank coarseDepth fineDepth) →
  consumerAtCode f (encode h) ≡ consumerAtHistory f h
consumerForward f h =
  cong f (Period.decodeEncodeNatPeriod270 (original h))

consumerBackward : ∀ {rank coarseDepth fineDepth Output} →
  (f : Nat → Output) →
  (h : EncodedArithmeticHistory rank coarseDepth fineDepth) →
  consumerAtHistory f (decode h) ≡ consumerAtCode f h
consumerBackward f h = refl

-- The caller's f is the real target consumer, not a dummy boolean.
actualMangoldtPairForward :
  ∀ {rank coarseDepth fineDepth} →
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  (h : ArithmeticHistory rank coarseDepth fineDepth) →
  consumerAtCode (Pair.actualPairConsumer space arith mangoldt) (encode h)
  ≡ consumerAtHistory (Pair.actualPairConsumer space arith mangoldt) h
actualMangoldtPairForward space arith mangoldt =
  consumerForward (Pair.actualPairConsumer space arith mangoldt)

-- Does not imply consumer descent through only a coarse address or
-- through a sign-only quotient. No prime-pair positivity theorem is claimed.
