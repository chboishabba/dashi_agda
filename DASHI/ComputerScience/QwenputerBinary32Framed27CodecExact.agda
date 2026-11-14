module DASHI.ComputerScience.QwenputerBinary32Framed27CodecExact where

-- Internal original owner: FixedNineBitFramed27WordStorageExact,
-- itself based on BinaryThreeBitTwoTritAntipodalCodecExact and
-- BinaryThreeBitTrit27FibreLiftExact. This module REUSES that proof.
-- Source context: Divyansh Agrawal, Qwenputer RV32 (2026);
-- RISC-V 32-bit machine words are binary. An alternative ternary
-- storage representation is a DASHI extension, NOT Qwenputer hardware.
-- Four 8-bit bytes are carried by 4 padded 9-bit words and then four
-- framed ternary-27 cells x 3. No physical density benefit is claimed.

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.ComputerScience.FixedNineBitFramed27WordStorageExact as W

record Byte8 : Set where
  constructor byte8
  field
    b0 b1 b2 b3 b4 b5 b6 b7 : Bool
open Byte8 public

paddedWord : Byte8 → W.BinaryWord9
paddedWord b =
  W.binaryWord9 (b0 b) (b1 b) (b2 b) (b3 b)
    (b4 b) (b5 b) (b6 b) (b7 b) false

unpadWord : W.BinaryWord9 → Byte8
unpadWord w =
  byte8 (W.b0 w) (W.b1 w) (W.b2 w) (W.b3 w)
    (W.b4 w) (W.b5 w) (W.b6 w) (W.b7 w)

bytePaddingRoundTrip : (b : Byte8) → unpadWord (paddedWord b) ≡ b
bytePaddingRoundTrip (byte8 a b c d e f g h) = refl

encodeByte27 : Byte8 → W.Ternary27Word3
encodeByte27 byte = W.binaryWord9ToTernary27 (paddedWord byte)

decodeByte27 : W.Ternary27Word3 → Byte8
decodeByte27 encoded =
  unpadWord (W.ternary27ToBinaryWord9 encoded)

byte27RoundTrip : (b : Byte8) → decodeByte27 (encodeByte27 b) ≡ b
byte27RoundTrip b
  rewrite W.binaryWordToTernaryRoundTrip (paddedWord b)
  = bytePaddingRoundTrip b

record BinaryWord32 : Set where
  constructor binaryWord32
  field
    byte0 byte1 byte2 byte3 : Byte8
open BinaryWord32 public

record FramedTernary32 : Set where
  constructor framedTernary32
  field
    cell0 cell1 cell2 cell3 : W.Ternary27Word3
open FramedTernary32 public

encode32 : BinaryWord32 → FramedTernary32
encode32 w = framedTernary32
  (encodeByte27 (byte0 w)) (encodeByte27 (byte1 w))
  (encodeByte27 (byte2 w)) (encodeByte27 (byte3 w))

decode32 : FramedTernary32 → BinaryWord32
decode32 w = binaryWord32
  (decodeByte27 (cell0 w)) (decodeByte27 (cell1 w))
  (decodeByte27 (cell2 w)) (decodeByte27 (cell3 w))

word32RoundTrip :
  (word : BinaryWord32) → decode32 (encode32 word) ≡ word
word32RoundTrip (binaryWord32 a b c d)
  rewrite byte27RoundTrip a
        | byte27RoundTrip b
        | byte27RoundTrip c
        | byte27RoundTrip d = refl

-- Byte order is held explicitly by field order; neither this codec nor
-- its parent infers a real RISC-V machine's endianness or instruction
-- addressing. The actual reference decoder must supply that bridge.
record ByteCodecBoundary : Set where
  constructor byteCodecBoundary
  field
    all32BitWordsReconstructFromFramedTernary : Bool
    bytePaddingIsFixedAtZero : Bool
    qwenputerRV32EndiannessWeld : Bool
    fullISAExecutionPreservation : Bool
    measuredPhysicalStorageSavings : Bool

canonicalByteCodecBoundary : ByteCodecBoundary
canonicalByteCodecBoundary =
  byteCodecBoundary true true false false false
