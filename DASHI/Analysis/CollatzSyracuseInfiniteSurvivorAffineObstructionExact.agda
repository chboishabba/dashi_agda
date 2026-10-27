module DASHI.Analysis.CollatzSyracuseInfiniteSurvivorAffineObstructionExact where

------------------------------------------------------------------------
-- ALL-HORIZON SURVIVOR -> AFFINE CORRECTION OBSTRUCTION
--
-- For one literal start x, assume survival through every horizon.  At any
-- horizon whose actual parity word is multiplicatively contracting,
--
--   2^m = 3^(ones w) + g,   g > 0,
--
-- survival forces
--
--   g*x <= A(w).
--
-- Equivalently, finding one actual contracting prefix with A(w) < g*x refutes
-- the infinite survivor and gives literal strict descent at that horizon.
-- This is an exact arithmetic normal form of the remaining terminal wall, not
-- a new proof of universal Collatz stopping.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_<_; _≤_)
open import Data.Empty using (⊥)
open import Data.Product using (Σ)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseParadoxicalPrefixExact as Paradox
import DASHI.Analysis.CollatzSyracuseResidualInverseLimitObstructionExact as Inverse

allHorizonSurvivorMakesContractingPrefixParadoxical :
  {x : Syracuse.PositiveNat} {m : Nat} →
  Inverse.AllHorizonSurvivor x →
  Paradox.ContractingCoefficientGap (Itinerary.parityWord m x) →
  Paradox.ParadoxicalPrefix x m
allHorizonSurvivorMakesContractingPrefixParadoxical {m = m} survives coefficient =
  record
    { Paradox.coefficientGap = coefficient
    ; Paradox.noLiteralDescent = survives m
    }

contractingSurvivorForcesCorrectionDominance :
  {x : Syracuse.PositiveNat} {m : Nat} →
  Inverse.AllHorizonSurvivor x →
  (coefficient :
    Paradox.ContractingCoefficientGap (Itinerary.parityWord m x)) →
  Paradox.gap coefficient * Syracuse.toNat x
  ≤ Affine.affineAdditiveTerm (Itinerary.parityWord m x)
contractingSurvivorForcesCorrectionDominance survives coefficient =
  Paradox.paradoxicalPrefixForcesCorrectionDominance
    (allHorizonSurvivorMakesContractingPrefixParadoxical
      survives coefficient)

contractingSurvivorStartBoundedByCorrection :
  {x : Syracuse.PositiveNat} {m : Nat} →
  Inverse.AllHorizonSurvivor x →
  (coefficient :
    Paradox.ContractingCoefficientGap (Itinerary.parityWord m x)) →
  Syracuse.toNat x
  ≤ Affine.affineAdditiveTerm (Itinerary.parityWord m x)
contractingSurvivorStartBoundedByCorrection survives coefficient =
  Paradox.paradoxicalPrefixStartBoundedByCorrection
    (allHorizonSurvivorMakesContractingPrefixParadoxical
      survives coefficient)

oneContractingCorrectionFitRefutesInfiniteSurvivor :
  {x : Syracuse.PositiveNat} {m : Nat} →
  (coefficient :
    Paradox.ContractingCoefficientGap (Itinerary.parityWord m x)) →
  Affine.affineAdditiveTerm (Itinerary.parityWord m x)
    < Paradox.gap coefficient * Syracuse.toNat x →
  Inverse.AllHorizonSurvivor x →
  ⊥
oneContractingCorrectionFitRefutesInfiniteSurvivor {x} {m} coefficient correctionFits survives =
  survives m
    (Paradox.contractingCorrectionFitImpliesLiteralDescent
      (Itinerary.parityWord m x)
      coefficient
      x
      correctionFits
      refl)

------------------------------------------------------------------------
-- Exact universal source interface for the unresolved arithmetic leaf.
--
-- This decomposes the terminal exact affine margin into:
--   1. a positive coefficient gap on the ACTUAL parity word;
--   2. the correction fitting inside that gap at the SAME start.
-- It is intentionally not marked paid.
------------------------------------------------------------------------

record UniversalContractingCorrectionEscapeSource : Set₁ where
  field
    escape :
      (x : Syracuse.PositiveNat) →
      1 < Syracuse.toNat x →
      Σ Nat λ m →
      Σ (Paradox.ContractingCoefficientGap (Itinerary.parityWord m x)) λ coefficient →
        Affine.affineAdditiveTerm (Itinerary.parityWord m x)
        < Paradox.gap coefficient * Syracuse.toNat x

record InfiniteSurvivorAffineBoundary : Set where
  constructor infiniteSurvivorAffineBoundary
  field
    allHorizonToParadoxicalContractingPrefixPaid : Nat
    contractingSurvivorCorrectionDominancePaid : Nat
    contractingSurvivorStartBoundPaid : Nat
    oneContractingCorrectionFitRefutesInfiniteSurvivorPaid : Nat
    universalEscapeInterfacePaid : Nat

    universalContractingCorrectionEscapeProducerPaid : Nat
    almostAllDensityPromotesUniversalEscape : Nat
    finiteVerificationPromotesUniversalEscape : Nat
    nearResonanceClassificationAlonePromotesUniversalEscape : Nat

canonicalInfiniteSurvivorAffineBoundary : InfiniteSurvivorAffineBoundary
canonicalInfiniteSurvivorAffineBoundary =
  infiniteSurvivorAffineBoundary
    1 1 1 1 1
    0 0 0 0
