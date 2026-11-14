{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthPayloadSimulationExact where

------------------------------------------------------------------------
-- F1 ACTUAL ALL-k PHYSICAL GAMMA PAYLOAD-LOOP SIMULATION.
--
-- Genuine finite instruction table:
-- Karp21NativeGammaAllLengthFiniteTablePhysicalExact.gammaAllLengthProgram.
-- We prove that, ONCE the k prefix marks and gamma separator have
-- brought the physical head to the first payload symbol, exactly k
-- physical instructions consume ANY original k-bit binary payload,
-- preserving suffix and transcribing each bit onto the work tape.
--
-- Source gamma/encoding: Karp21GammaBinaryNativePayloadExact,
-- existing readGammaBinaryPayloadExact, no numerical Nat parser.
--
-- The explicit work tape is a zipper with k Mark tally cells,
-- and after k steps is Blank with reversed payload to the right.
-- This is NOT a complete all-k prefix-to-payload bisimulation or
-- full N21 bit-clock; the first-prefix, separator, multi-token
-- original N21 and F2/F3/F4 work remain open.
--
-- Kernel/source trust: new Agda --safe proof, still needs exact-head
-- pinned Agda 2.9 and transitive trust acceptance; no postulates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.List.Base as List
import Data.Vec.Base as Vec

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21NativeBitTapePhysicalMachineExact as Tape
import DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthFiniteTablePhysicalExact as Gamma

marks : Nat → List Tape.Cell
marks zero = []
marks (suc n) = Tape.Mark ∷ marks n

workWithRemainingMarks :
  Nat → List Tape.Cell → Tape.Tape
workWithRemainingMarks zero right =
  Tape.tape [] Tape.Blank right
workWithRemainingMarks (suc n) right =
  Tape.tape (marks n) Tape.Mark right

inputAt :
  List Tape.Cell → Word.BitWord → Tape.Tape
inputAt left [] = Tape.tape left Tape.Blank []
inputAt left (bit ∷ suffix) =
  Tape.tape left (Tape.encodeBit bit) (Tape.encodeBits suffix)

payloadConfiguration :
  List Tape.Cell → List Tape.Cell →
  Word.BitWord → Word.BitWord →
  Tape.Configuration 3 1
payloadConfiguration left right payload suffix =
  Tape.config Gamma.payloadState
    (inputAt left (List._++_ payload suffix))
    (workWithRemainingMarks (List.length payload) right
      Vec.∷ Vec.[])
    false

-- One ACTUAL stored physical table transition consumes the first
-- payload symbol, shifts its input head by one, writes it to the
-- original last Mark, and shifts the work head back one cell.
-- Cases split only on the literal next source input symbol.
onePhysicalPayloadBit :
  (left right : List Tape.Cell)
  (bit : Bool)
  (rest suffix : Word.BitWord) →
  Tape.machineStep Gamma.gammaAllLengthProgram
    (payloadConfiguration left right (bit ∷ rest) suffix)
  ≡
  payloadConfiguration
    (Tape.encodeBit bit ∷ left)
    (Tape.encodeBit bit ∷ right)
    rest suffix
onePhysicalPayloadBit left right false [] [] = refl
onePhysicalPayloadBit left right false [] (false ∷ suffix) = refl
onePhysicalPayloadBit left right false [] (true ∷ suffix) = refl
onePhysicalPayloadBit left right false (next ∷ rest) suffix = refl
onePhysicalPayloadBit left right true [] [] = refl
onePhysicalPayloadBit left right true [] (false ∷ suffix) = refl
onePhysicalPayloadBit left right true [] (true ∷ suffix) = refl
onePhysicalPayloadBit left right true (next ∷ rest) suffix = refl

pushEncoded :
  Word.BitWord → List Tape.Cell → List Tape.Cell
pushEncoded [] prior = prior
pushEncoded (bit ∷ rest) prior =
  pushEncoded rest (Tape.encodeBit bit ∷ prior)

-- Fully arbitrary-length physical payload loop:
-- exactly length(payload) instructions, suffix untouched,
-- no state oracle and no source Nat allocation.
physicalAllLengthPayloadLoopExact :
  (left right : List Tape.Cell)
  (payload suffix : Word.BitWord) →
  Tape.machineRun (List.length payload)
    Gamma.gammaAllLengthProgram
    (payloadConfiguration left right payload suffix)
  ≡
  payloadConfiguration
    (pushEncoded payload left)
    (pushEncoded payload right)
    [] suffix
physicalAllLengthPayloadLoopExact left right [] suffix = refl
physicalAllLengthPayloadLoopExact
  left right (bit ∷ rest) suffix
  rewrite onePhysicalPayloadBit left right bit rest suffix =
  physicalAllLengthPayloadLoopExact
    (Tape.encodeBit bit ∷ left)
    (Tape.encodeBit bit ∷ right)
    rest suffix
