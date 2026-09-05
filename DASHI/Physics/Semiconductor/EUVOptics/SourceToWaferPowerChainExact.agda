{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.EUVOptics.SourceToWaferPowerChainExact where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Multiplicative source-to-wafer energy accounting.
--
-- Each transfer element owns only a numerator/denominator retention factor.
-- The product is deliberately agnostic about the physical mechanism: collector
-- acceptance, mirror reflection, mask reflection, pupil clipping, contamination
-- or other loss mechanisms may later receive separate scientific producers.

record TransferFactor : Set where
  constructor transferFactor
  field
    numerator   : Nat
    denominator : Nat

open TransferFactor public

record EnergyTransferStage : Set where
  constructor energyTransferStage
  field
    inputPowerCoordinate  : Nat
    outputPowerCoordinate : Nat
    transfer              : TransferFactor
    transferWitness       : outputPowerCoordinate * denominator transfer ≡
                            inputPowerCoordinate * numerator transfer

open EnergyTransferStage public

productNumerators : List TransferFactor → Nat
productNumerators [] = 1
productNumerators (x ∷ xs) = numerator x * productNumerators xs

productDenominators : List TransferFactor → Nat
productDenominators [] = 1
productDenominators (x ∷ xs) = denominator x * productDenominators xs

-- A generic chain does not identify where a loss occurred.  It only owns the
-- compositional accounting boundary.  Mechanistic attribution is a separate
-- proposition and must be supplied by a later producer.
record TransferChain : Set where
  constructor transferChain
  field
    factors : List TransferFactor

open TransferChain public

-- Regression: three idealized 70%-retention reflections give 343/1000.
-- This deliberately uses a short synthetic chain rather than asserting the
-- topology of a particular production scanner.

threeIdealMirrors : TransferChain
threeIdealMirrors =
  transferChain
    (transferFactor 70 100 ∷
     transferFactor 70 100 ∷
     transferFactor 70 100 ∷ [])

threeMirrorNumeratorsExact :
  productNumerators (factors threeIdealMirrors) ≡ 343000
threeMirrorNumeratorsExact = refl

threeMirrorDenominatorsExact :
  productDenominators (factors threeIdealMirrors) ≡ 1000000
threeMirrorDenominatorsExact = refl
