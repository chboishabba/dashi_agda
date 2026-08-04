module DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- PURPOSE
-- Define the actual signed factorial terms for sine and cosine and prove their
-- parity on the concrete Bishop-real carrier.  This supplies the term-family
-- hypotheses consumed by the round-ten transformed-convergence theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (1ℚᵘ)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as Recurrence
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as ParityLimit
open import DASHI.Physics.YangMills.CompactLieProofLevel

bishopMinusOne : BishopReal.ℝ
bishopMinusOne = BishopReal.- BishopReal.1ℝ

alternatingSign : Nat → BishopReal.ℝ
alternatingSign index = BishopReal.pow bishopMinusOne index

sineSignedTerm cosineSignedTerm :
  BishopReal.ℝ → Nat → BishopReal.ℝ
sineSignedTerm value index =
  BishopReal._*_
    (alternatingSign index)
    (BishopReal._*_
      (BishopReal._⋆
        (Estimates.inverseFactorialRational
          (Estimates.oddExponent index)))
      (BishopReal.pow value (Estimates.oddExponent index)))

cosineSignedTerm value index =
  BishopReal._*_
    (alternatingSign index)
    (BishopReal._*_
      (BishopReal._⋆
        (Estimates.inverseFactorialRational
          (Estimates.evenExponent index)))
      (BishopReal.pow value (Estimates.evenExponent index)))

negatedSquareEquivalentSquare :
  ∀ value →
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal.- value)
      (BishopReal.- value))
    (BishopReal._*_ value value)
negatedSquareEquivalentSquare value =
  let open BishopProperties.ℝ-Solver
  in solve 1
      (λ x → (⊝ x) ⊗ (⊝ x) ⊜ x ⊗ x)
      BishopProperties.≃-refl
      value

negatedProductEquivalentNegativeProduct :
  ∀ left right →
  BishopReal._≃_
    (BishopReal._*_ (BishopReal.- left) right)
    (BishopReal.- (BishopReal._*_ left right))
negatedProductEquivalentNegativeProduct left right =
  let open BishopProperties.ℝ-Solver
  in solve 2
      (λ x y → (⊝ x) ⊗ y ⊜ ⊝ (x ⊗ y))
      BishopProperties.≃-refl
      left right

oddPowerNegation :
  ∀ value index →
  BishopReal._≃_
    (BishopReal.pow
      (BishopReal.- value)
      (Estimates.oddExponent index))
    (BishopReal.-
      (BishopReal.pow value (Estimates.oddExponent index)))
oddPowerNegation value zero =
  let open BishopProperties.ℝ-Solver
  in solve 1
      (λ x → Κ 1ℚᵘ ⊗ (⊝ x) ⊜ ⊝ (Κ 1ℚᵘ ⊗ x))
      BishopProperties.≃-refl
      value
oddPowerNegation value (suc index) =
  let
    exponent = Estimates.oddExponent index
    oldPower = BishopReal.pow value exponent
    square = BishopReal._*_ value value
  in
  BishopProperties.≃-trans
    (Recurrence.powTwoStep (BishopReal.- value) exponent)
    (BishopProperties.≃-trans
      (BishopProperties.*-cong
        (oddPowerNegation value index)
        (negatedSquareEquivalentSquare value))
      (BishopProperties.≃-trans
        (negatedProductEquivalentNegativeProduct oldPower square)
        (BishopProperties.-‿cong
          (BishopProperties.≃-symm
            (Recurrence.powTwoStep value exponent)))))

evenPowerNegation :
  ∀ value index →
  BishopReal._≃_
    (BishopReal.pow
      (BishopReal.- value)
      (Estimates.evenExponent index))
    (BishopReal.pow value (Estimates.evenExponent index))
evenPowerNegation value zero = BishopProperties.≃-refl
evenPowerNegation value (suc index) =
  let exponent = Estimates.evenExponent index
  in
  BishopProperties.≃-trans
    (Recurrence.powTwoStep (BishopReal.- value) exponent)
    (BishopProperties.≃-trans
      (BishopProperties.*-cong
        (evenPowerNegation value index)
        (negatedSquareEquivalentSquare value))
      (BishopProperties.≃-symm
        (Recurrence.powTwoStep value exponent)))

sineSignedTermCongruent :
  ∀ {left right} →
  BishopReal._≃_ left right →
  ∀ index →
  BishopReal._≃_
    (sineSignedTerm left index)
    (sineSignedTerm right index)
sineSignedTermCongruent leftEquivalentRight index =
  BishopProperties.*-congˡ
    (BishopProperties.*-congˡ
      (BishopProperties.pow-cong
        (Estimates.oddExponent index)
        leftEquivalentRight))

cosineSignedTermCongruent :
  ∀ {left right} →
  BishopReal._≃_ left right →
  ∀ index →
  BishopReal._≃_
    (cosineSignedTerm left index)
    (cosineSignedTerm right index)
cosineSignedTermCongruent leftEquivalentRight index =
  BishopProperties.*-congˡ
    (BishopProperties.*-congˡ
      (BishopProperties.pow-cong
        (Estimates.evenExponent index)
        leftEquivalentRight))

sineSignedTermNegation :
  ∀ value index →
  BishopReal._≃_
    (sineSignedTerm (BishopReal.- value) index)
    (BishopReal.- (sineSignedTerm value index))
sineSignedTermNegation value index =
  let
    sign = alternatingSign index
    coefficient =
      BishopReal._⋆
        (Estimates.inverseFactorialRational
          (Estimates.oddExponent index))
    power = BishopReal.pow value (Estimates.oddExponent index)
  in
  BishopProperties.≃-trans
    (BishopProperties.*-congˡ
      (BishopProperties.*-congˡ
        (oddPowerNegation value index)))
    (let open BishopProperties.ℝ-Solver
     in solve 3
        (λ s c p → s ⊗ (c ⊗ (⊝ p)) ⊜ ⊝ (s ⊗ (c ⊗ p)))
        BishopProperties.≃-refl
        sign coefficient power)

cosineSignedTermNegation :
  ∀ value index →
  BishopReal._≃_
    (cosineSignedTerm (BishopReal.- value) index)
    (cosineSignedTerm value index)
cosineSignedTermNegation value index =
  BishopProperties.*-congˡ
    (BishopProperties.*-congˡ
      (evenPowerNegation value index))

concreteSineOddTermFamily :
  ParityLimit.BishopOddTermFamily sineSignedTerm
concreteSineOddTermFamily = record
  { termCongruent = sineSignedTermCongruent
  ; termOdd = sineSignedTermNegation
  }

concreteCosineEvenTermFamily :
  ParityLimit.BishopEvenTermFamily cosineSignedTerm
concreteCosineEvenTermFamily = record
  { termCongruent = cosineSignedTermCongruent
  ; termEven = cosineSignedTermNegation
  }

bishopOddEvenPowerNegationLevel : ProofLevel
bishopOddEvenPowerNegationLevel = machineChecked

bishopConcreteSineCosineTermParityLevel : ProofLevel
bishopConcreteSineCosineTermParityLevel = machineChecked
