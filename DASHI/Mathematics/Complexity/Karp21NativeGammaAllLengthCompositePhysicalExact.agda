{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthCompositePhysicalExact where

------------------------------------------------------------------------
-- F1.4 SOURCE-ORIGINAL ALL-k PHYSICAL GAMMA POSITIVE-WORD COMPOSITION.
--
-- This theorem is an actual composition over Tape.machineRun of FOUR
-- previously source-written physical transition proofs, not a logical
-- receipt/predicate or replacement machine:
-- * original B0 prefix for exactly k steps;
-- * separator for one step;
-- * k payload steps over the same payload source word;
-- * finish without consuming ANY untouched source suffix.
--
-- For k>=1 this gives a single literal fuelled physical run
-- with k + (1 + (k + 1)) table instructions. The input
-- 0^k ++ 1 :: payload ++ suffix encodes ORIGINAL gamma.
-- Positive output is the precise physical halted configuration
-- (reversed payload bits to the right of a work-head blank).
--
-- For k=0 the original table halts after one separator and the
-- original all-length gamma parser consumes the same B1 source.
--
-- This is NOT a full total parser: malformed source words, an
-- independently typed acceptance/reject bit, repeated N21 fields,
-- physical complete heap accounting, F3 original FRACTRAN step and
-- the original F4 polynomial verifier clock remain separate OPEN
-- obligations. Source-written proof requires pinned Agda 2.9 check.
--
-- Original code and source priority: PR #1474 all-k native gamma,
-- PR #1502 stacked convergence; Karp (1972), Conway (1987).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.List.Base as List
import Data.Vec.Base as Vec

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Original
import DASHI.Mathematics.Complexity.Karp21NativeBitTapePhysicalMachineExact as Tape
import DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthFiniteTablePhysicalExact as Gamma
import DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthPrefixSimulationExact as Prefix
import DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthPayloadSimulationExact as Payload
import DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthSeparatorAndHaltExact as Join

-- Fuel costs are literal transition counts, not source-language
-- reductions. Splitting a physical run is proved by induction on
-- the FIRST run's fuel, for arbitrary literal local table programs.
physicalRunAdditionExact :
  {q k : Nat}
  (a b : Nat) (program : Tape.LocalProgram q k)
  (cfg : Tape.Configuration q k) →
  Tape.machineRun (a + b) program cfg
    ≡ Tape.machineRun b program
        (Tape.machineRun a program cfg)
physicalRunAdditionExact zero b program cfg = refl
physicalRunAdditionExact (suc a) b program cfg =
  physicalRunAdditionExact a b program (Tape.machineStep program cfg)

-- For every payload k=n+1>=1, all four physical stages combine
-- on the exact original encoded input, with the same input zipper,
-- not just on independent isomorphic example configurations.
physicalPositiveGammaStagesExact :
  (first : Bool) (rest suffix : Word.BitWord) →
  let n = List.length rest
      k = suc n
      payload = first ∷ rest
      inputWord =
        List._++_ (Original.zeroPrefix k)
          (true ∷ List._++_ payload suffix)
      start = Gamma.startPhysicalGamma inputWord
      left = Tape.B1 ∷ Prefix.pushZeros n (Tape.B0 ∷ [])
      workRight = Tape.Blank ∷ []
  in
  Tape.machineStep Gamma.gammaAllLengthProgram
    (Tape.machineRun k Gamma.gammaAllLengthProgram
      (Tape.machineStep Gamma.gammaAllLengthProgram
        (Tape.machineRun k Gamma.gammaAllLengthProgram start)))
  ≡
  Tape.config Gamma.payloadState
    (Payload.inputAt (Payload.pushEncoded payload left) suffix)
    (Payload.workWithRemainingMarks zero
      (Payload.pushEncoded payload workRight) Vec.∷ Vec.[])
    true
physicalPositiveGammaStagesExact first rest suffix
  rewrite
    Prefix.physicalWholePrefixZeroRunExact
      (List.length rest) (first ∷ rest) suffix
  | Join.wholePrefixWorkMarksExact (List.length rest)
  | Join.physicalSeparatorToOriginalPayload
      (Prefix.pushZeros (List.length rest) (Tape.B0 ∷ []))
      first rest suffix
  | Payload.physicalAllLengthPayloadLoopExact
      (Tape.B1 ∷ Prefix.pushZeros (List.length rest) (Tape.B0 ∷ []))
      (Tape.Blank ∷ [])
      (first ∷ rest) suffix
  | Join.physicalGammaCompletionPreservesSuffix
      (Payload.pushEncoded (first ∷ rest)
        (Tape.B1 ∷ Prefix.pushZeros (List.length rest) (Tape.B0 ∷ [])))
      (Payload.pushEncoded (first ∷ rest) (Tape.Blank ∷ []))
      suffix
  = refl

-- A single arbitrary-positive-k machineRun, not four isolated
-- theorem statements. The explicit total fuel is k+(1+(k+1)),
-- corresponding to 2k+2 literal physical table instructions.
physicalAllLengthGammaRunSameOriginalPositive :
  (first : Bool) (rest suffix : Word.BitWord) →
  let n = List.length rest
      k = suc n
      payload = first ∷ rest
      start = Gamma.startPhysicalGamma
        (List._++_ (Original.zeroPrefix k)
          (true ∷ List._++_ payload suffix))
      left = Tape.B1 ∷ Prefix.pushZeros n (Tape.B0 ∷ [])
      workRight = Tape.Blank ∷ []
  in
  Tape.machineRun (k + (suc (k + suc zero)))
    Gamma.gammaAllLengthProgram start
  ≡
  Tape.config Gamma.payloadState
    (Payload.inputAt (Payload.pushEncoded payload left) suffix)
    (Payload.workWithRemainingMarks zero
      (Payload.pushEncoded payload workRight) Vec.∷ Vec.[])
    true
physicalAllLengthGammaRunSameOriginalPositive first rest suffix
  rewrite
    physicalRunAdditionExact
      (suc (List.length rest))
      (suc ((suc (List.length rest)) + suc zero))
      Gamma.gammaAllLengthProgram
      (Gamma.startPhysicalGamma
        (List._++_ (Original.zeroPrefix (suc (List.length rest)))
          (true ∷ List._++_ (first ∷ rest) suffix)))
  | physicalRunAdditionExact
      (suc zero)
      ((suc (List.length rest)) + suc zero)
      Gamma.gammaAllLengthProgram
      (Tape.machineRun (suc (List.length rest))
        Gamma.gammaAllLengthProgram
        (Gamma.startPhysicalGamma
          (List._++_ (Original.zeroPrefix (suc (List.length rest)))
            (true ∷ List._++_ (first ∷ rest) suffix))))
  | physicalRunAdditionExact
      (suc (List.length rest))
      (suc zero)
      Gamma.gammaAllLengthProgram
      (Tape.machineStep Gamma.gammaAllLengthProgram
        (Tape.machineRun (suc (List.length rest))
          Gamma.gammaAllLengthProgram
          (Gamma.startPhysicalGamma
            (List._++_ (Original.zeroPrefix (suc (List.length rest)))
              (true ∷ List._++_ (first ∷ rest) suffix)))))
  | physicalPositiveGammaStagesExact first rest suffix
  = refl
