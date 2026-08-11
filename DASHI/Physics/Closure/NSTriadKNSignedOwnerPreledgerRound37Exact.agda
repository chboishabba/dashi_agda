module DASHI.Physics.Closure.NSTriadKNSignedOwnerPreledgerRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- The final nine-owner theorem must bound positive production, but taking a
-- positive part or an absolute value too early can erase exact cancellations.
-- This module therefore introduces a signed *preledger* before the existing
-- admissible-owner quotient.
--
-- For one owner
--
--   Delta = production - cancellation.
--
-- Reversing production/cancellation negates Delta exactly.  More importantly,
-- an internal transfer tau credited to one owner's production and debited as
-- another owner's cancellation leaves the combined signed balance invariant:
--
--   ((A+tau)-B) + (C-(D+tau))
--     = (A-B) + (C-D).
--
-- This is the exact algebraic reason to retain the signed fine ledger upstream
-- of the positive owner tax.  No cross-owner cancellation is assumed in the
-- final viscosity absorption theorem; the module merely prevents information
-- from being destroyed before one has proved whether it cancels.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record SignedOwnerCell : Set where
  constructor signed-owner-cell
  field
    production cancellation : ℚ

open SignedOwnerCell public

signedNet : SignedOwnerCell → ℚ
signedNet cell = production cell - cancellation cell

reverseOwnerCell : SignedOwnerCell → SignedOwnerCell
reverseOwnerCell cell =
  signed-owner-cell (cancellation cell) (production cell)

reverseOwnerNegatesNet : ∀ cell →
  signedNet (reverseOwnerCell cell) ≡ - signedNet cell
reverseOwnerNegatesNet cell =
  solve (production cell ∷ cancellation cell ∷ [])

sumSignedNet : List SignedOwnerCell → ℚ
sumSignedNet [] = 0ℚ
sumSignedNet (cell ∷ rest) = signedNet cell + sumSignedNet rest

record SignedOwnerPair : Set where
  constructor signed-owner-pair
  field
    left right : SignedOwnerCell

open SignedOwnerPair public

pairNet : SignedOwnerPair → ℚ
pairNet pair = signedNet (left pair) + signedNet (right pair)

internalTransfer : ℚ → SignedOwnerPair → SignedOwnerPair
internalTransfer transfer pair =
  signed-owner-pair
    (signed-owner-cell
      (production (left pair) + transfer)
      (cancellation (left pair)))
    (signed-owner-cell
      (production (right pair))
      (cancellation (right pair) + transfer))

internalTransferPreservesPairNet : ∀ transfer pair →
  pairNet (internalTransfer transfer pair) ≡ pairNet pair
internalTransferPreservesPairNet transfer pair =
  solve
    ( production (left pair)
    ∷ cancellation (left pair)
    ∷ production (right pair)
    ∷ cancellation (right pair)
    ∷ transfer
    ∷ [])

oppositePair : ℚ → SignedOwnerPair
oppositePair amount =
  signed-owner-pair
    (signed-owner-cell amount 0ℚ)
    (signed-owner-cell 0ℚ amount)

oppositePairCancelsExactly : ∀ amount →
  pairNet (oppositePair amount) ≡ 0ℚ
oppositePairCancelsExactly amount = solve (amount ∷ [])

record SignedToPositiveOwnerQuotient : Set₁ where
  field
    PositiveCharge : Set
    coarseCharge : SignedOwnerCell → PositiveCharge

    -- Deliberately no injectivity field: the positive owner language is a
    -- quotient/majorant and need not remember which signed cancellation was
    -- present upstream.

open SignedToPositiveOwnerQuotient public

signedOwnerPreledgerClosed : Bool
signedOwnerPreledgerClosed = true

physicalNineOwnerSignedPreledgerConstructed : Bool
physicalNineOwnerSignedPreledgerConstructed = false

signedOwnerPreledgerClosedIsTrue :
  signedOwnerPreledgerClosed ≡ true
signedOwnerPreledgerClosedIsTrue = refl
