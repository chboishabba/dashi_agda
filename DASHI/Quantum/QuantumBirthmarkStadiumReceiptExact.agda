{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkStadiumReceiptExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- BUNIMOVICH-STADIUM NUMERICAL EXAMPLE
--
-- These values are source-facing receipts from PRX Table I, not premises of
-- the universal RMT result.  We encode decimal data as scaled naturals so the
-- source values survive without importing a floating-point authority layer.
------------------------------------------------------------------------

record ScaledDecimal : Set where
  constructor scaled
  field
    mantissa : Nat
    scale10 : Nat

open ScaledDecimal public

decimalTenths : Nat → ScaledDecimal
decimalTenths n = scaled n 1

decimalHundredths : Nat → ScaledDecimal
decimalHundredths n = scaled n 2

-- First reported Table-I metric, soft-wall / hard-wall examples.
softA : ScaledDecimal
softA = decimalTenths 41

hardA : ScaledDecimal
hardA = decimalTenths 42

-- Overall QB enhancement for the most ergodic case D, close to the UQB
-- ensemble value 2.  A single packet may fall below the ensemble average.
softD : ScaledDecimal
softD = decimalHundredths 182

hardD : ScaledDecimal
hardD = decimalHundredths 198

-- Source-reported overall enhancement row for cases A-D.
softOverallA softOverallB softOverallC : ScaledDecimal
softOverallA = decimalHundredths 658
softOverallB = decimalHundredths 329
softOverallC = decimalHundredths 249

hardOverallA hardOverallB hardOverallC : ScaledDecimal
hardOverallA = decimalHundredths 825
hardOverallB = decimalHundredths 353
hardOverallC = decimalHundredths 266

record StadiumReceiptBoundary : Set where
  field
    softAndHardWallBothStudied : Bool
    initialGaussianWavePacket : Bool
    numericalPropagationUsed : Bool
    scarredCasesShowStrongerEnhancement : Bool
    chaoticCaseApproachesUniversalBackground : Bool
    stadiumDoesNotProveUniversalFactor : Bool
    singlePacketNeedNotEqualEnsembleAverage : Bool

stadiumReceiptBoundary : StadiumReceiptBoundary
stadiumReceiptBoundary = record
  { softAndHardWallBothStudied = true
  ; initialGaussianWavePacket = true
  ; numericalPropagationUsed = true
  ; scarredCasesShowStrongerEnhancement = true
  ; chaoticCaseApproachesUniversalBackground = true
  ; stadiumDoesNotProveUniversalFactor = true
  ; singlePacketNeedNotEqualEnsembleAverage = true
  }
