module DASHI.ComputerScience.QwenputerBinaryTernaryRamTraceSimulationExact where

-- Divyansh Agrawal, Qwenputer (2026): source context only,
-- https://github.com/divagr18/qwenputer
-- DASHI-owned transport proof. Prior exact implementation owners:
-- DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact
-- DASHI.ComputerScience.TemporalStorageFibreExact
-- and the tiny radix-neutral stored-program computer.
-- This is a pointwise binary/ternary RAM representation theorem.
-- It is not a benchmark or an ISA-level CPU equivalence.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.ComputerScience.QwenputerGatedDeltaArchitectureExact as RAM
import DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact as BT
import DASHI.Foundations.SSPTritCarrier as Trit

record WriteCommand : Set where
  constructor writeCommand
  field
    address : RAM.Location
    bit : Bool
open WriteCommand public

data Writes : Set where
  empty : Writes
  cons : WriteCommand → Writes → Writes

-- Pointwise decoder-based state relation. We do not assume function
-- extensionality or identify a ternary cell with a Boolean cell.
Related :
  RAM.Ram Bool → RAM.Ram Trit.SSPTrit → Set
Related source target =
  (a : RAM.Location) → BT.decodeEmbeddedBit (target a) ≡ source a

initialRelated : (source : RAM.Ram Bool) → Related source (RAM.embedBinaryRam source)
initialRelated source address =
  BT.binaryTernaryRoundTrip (source address)

writePreservesRelated :
  (source : RAM.Ram Bool) (target : RAM.Ram Trit.SSPTrit)
  (command : WriteCommand) →
  Related source target →
  Related
    (RAM.writeRam source (address command) (bit command))
    (RAM.writeRam target (address command) (BT.embedBit (bit command)))
writePreservesRelated source target command related queried
  with RAM.sameLocation (address command) queried
... | true = BT.binaryTernaryRoundTrip (bit command)
... | false = related queried

runBinary : Writes → RAM.Ram Bool → RAM.Ram Bool
runBinary empty source = source
runBinary (cons command rest) source =
  runBinary rest
    (RAM.writeRam source (address command) (bit command))

runTernary :
  Writes → RAM.Ram Trit.SSPTrit → RAM.Ram Trit.SSPTrit
runTernary empty target = target
runTernary (cons command rest) target =
  runTernary rest
    (RAM.writeRam target (address command) (BT.embedBit (bit command)))

runPreservesRelated :
  (commands : Writes) (source : RAM.Ram Bool)
  (target : RAM.Ram Trit.SSPTrit) →
  Related source target →
  Related (runBinary commands source) (runTernary commands target)
runPreservesRelated empty source target related = related
runPreservesRelated (cons command rest) source target related =
  runPreservesRelated rest
    (RAM.writeRam source (address command) (bit command))
    (RAM.writeRam target (address command) (BT.embedBit (bit command)))
    (writePreservesRelated source target command related)

binaryTernaryCompleteWriteTrace :
  (commands : Writes) (source : RAM.Ram Bool)
  (queried : RAM.Location) →
  BT.decodeEmbeddedBit
    (runTernary commands (RAM.embedBinaryRam source) queried)
    ≡ runBinary commands source queried
binaryTernaryCompleteWriteTrace commands source queried =
  runPreservesRelated commands source (RAM.embedBinaryRam source)
    (initialRelated source) queried

-- A second independent label on the same mathematical result:
-- the semantic state is the decoded memory, not the raw trit history.
-- The binary image never writes the neutral trit, but zero remains an
-- available trit for other ternary applications.
record TraceBoundary : Set where
  constructor traceBoundary
  field
    arbitraryFiniteWriteListSimulated : Bool
    pointwiseObservationsRecovered : Bool
    nativeTernaryALUSimulated : Bool
    realRv32CompiledWeightsSimulated : Bool

canonicalTraceBoundary : TraceBoundary
canonicalTraceBoundary = traceBoundary true true false false
