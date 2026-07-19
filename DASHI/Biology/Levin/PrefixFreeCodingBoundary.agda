module DASHI.Biology.Levin.PrefixFreeCodingBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Typed boundary for uniquely decodable variable-length binary codes.
--
-- The Kraft surface is represented as an explicit witness rather than
-- silently assumed.  This module does not claim an optimal code constructor.

record BinaryCode {ℓ : Set} : Set₁ where
  field
    Symbol : Set
    codeLength : Symbol → Nat
    encode : Symbol → List Bool
    prefixFreeWitness : Bool
    uniquelyDecodableWitness : Bool
    codeLengthMatchesEncoding : Bool

record KraftBoundary : Set where
  field
    finiteAlphabet : Bool
    nonzeroCodeLengths : Bool
    kraftSumAtMostOne : Bool
    prefixFreeFromKraftWitness : Bool
    converseConstructionWitness : Bool

record CodingOptimalityBoundary : Set where
  field
    sourceDistributionSpecified : Bool
    expectedLengthSpecified : Bool
    entropyLowerBoundSpecified : Bool
    blockCodingAllowed : Bool
    asymptoticLimitSpecified : Bool
    noSingleMessageOverfit : Bool
    noOptimalityWithoutWitness : Bool
    interpretation : String

canonicalKraftBoundary : KraftBoundary
canonicalKraftBoundary = record
  { finiteAlphabet = true
  ; nonzeroCodeLengths = true
  ; kraftSumAtMostOne = true
  ; prefixFreeFromKraftWitness = false
  ; converseConstructionWitness = false
  }

canonicalCodingOptimalityBoundary : CodingOptimalityBoundary
canonicalCodingOptimalityBoundary = record
  { sourceDistributionSpecified = true
  ; expectedLengthSpecified = true
  ; entropyLowerBoundSpecified = true
  ; blockCodingAllowed = true
  ; asymptoticLimitSpecified = true
  ; noSingleMessageOverfit = true
  ; noOptimalityWithoutWitness = true
  ; interpretation = "Prefix-free coding supplies unambiguous parsing; optimality additionally requires a source model, expected-length objective, and an explicit coding theorem witness"
  }
