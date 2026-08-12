module DASHI.Core.MinimalSufficientResidual where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

cong :
  ∀ {A B : Set} {x y : A} →
  (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans :
  ∀ {A : Set} {x y z : A} →
  x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

------------------------------------------------------------------------
-- Minimal sufficient residual: finite exact witness.
--
-- For a four-state fine carrier projected to its first bit, exact reopening
-- necessarily requires the residual carrier to distinguish the two hidden
-- states in each coarse fibre.  A single Bool hidden-bit residual suffices.
--
-- This is deliberately a finite lower-bound theorem, not a claim that every
-- application admits a unique globally minimal residual or an MDL optimum.
------------------------------------------------------------------------

data FineBitState : Set where
  fine00 fine01 fine10 fine11 : FineBitState

coarseFirstBit : FineBitState → Bool
coarseFirstBit fine00 = false
coarseFirstBit fine01 = false
coarseFirstBit fine10 = true
coarseFirstBit fine11 = true

hiddenSecondBit : FineBitState → Bool
hiddenSecondBit fine00 = false
hiddenSecondBit fine01 = true
hiddenSecondBit fine10 = false
hiddenSecondBit fine11 = true

reopenFromHiddenBit : Bool → Bool → FineBitState
reopenFromHiddenBit false false = fine00
reopenFromHiddenBit false true = fine01
reopenFromHiddenBit true false = fine10
reopenFromHiddenBit true true = fine11

canonicalBinaryResidualReopensExactly :
  (state : FineBitState) →
  reopenFromHiddenBit (coarseFirstBit state) (hiddenSecondBit state) ≡ state
canonicalBinaryResidualReopensExactly fine00 = refl
canonicalBinaryResidualReopensExactly fine01 = refl
canonicalBinaryResidualReopensExactly fine10 = refl
canonicalBinaryResidualReopensExactly fine11 = refl

record ExactFirstBitResidual (Receipt : Set) : Set₁ where
  constructor exactFirstBitResidual
  field
    receipt : FineBitState → Receipt
    reopen : Bool → Receipt → FineBitState
    reopenExact :
      (state : FineBitState) →
      reopen (coarseFirstBit state) (receipt state) ≡ state

open ExactFirstBitResidual public

canonicalBoolResidual : ExactFirstBitResidual Bool
canonicalBoolResidual =
  exactFirstBitResidual
    hiddenSecondBit
    reopenFromHiddenBit
    canonicalBinaryResidualReopensExactly

fine00IsNotFine01 : fine00 ≡ fine01 → ⊥
fine00IsNotFine01 ()

fine10IsNotFine11 : fine10 ≡ fine11 → ⊥
fine10IsNotFine11 ()

leftFibreRequiresDistinctResiduals :
  ∀ {Receipt : Set}
    (residual : ExactFirstBitResidual Receipt) →
  receipt residual fine00 ≡ receipt residual fine01 →
  ⊥
leftFibreRequiresDistinctResiduals residual receiptsEqual =
  fine00IsNotFine01
    (trans
      (sym (reopenExact residual fine00))
      (trans
        (cong (reopen residual false) receiptsEqual)
        (reopenExact residual fine01)))

rightFibreRequiresDistinctResiduals :
  ∀ {Receipt : Set}
    (residual : ExactFirstBitResidual Receipt) →
  receipt residual fine10 ≡ receipt residual fine11 →
  ⊥
rightFibreRequiresDistinctResiduals residual receiptsEqual =
  fine10IsNotFine11
    (trans
      (sym (reopenExact residual fine10))
      (trans
        (cong (reopen residual true) receiptsEqual)
        (reopenExact residual fine11)))

record HasSeparatedReceiptPair (Receipt : Set) : Set where
  constructor hasSeparatedReceiptPair
  field
    leftReceipt rightReceipt : Receipt
    receiptsDistinct : leftReceipt ≡ rightReceipt → ⊥

open HasSeparatedReceiptPair public

anyExactResidualMustSeparateAHiddenPair :
  ∀ {Receipt : Set} →
  ExactFirstBitResidual Receipt →
  HasSeparatedReceiptPair Receipt
anyExactResidualMustSeparateAHiddenPair residual =
  hasSeparatedReceiptPair
    (receipt residual fine00)
    (receipt residual fine01)
    (leftFibreRequiresDistinctResiduals residual)

boolResidualSuppliesTheRequiredSeparation :
  HasSeparatedReceiptPair Bool
boolResidualSuppliesTheRequiredSeparation =
  anyExactResidualMustSeparateAHiddenPair canonicalBoolResidual

record MinimalBinaryResidualWitness : Set₁ where
  constructor minimalBinaryResidualWitness
  field
    sufficientResidual : ExactFirstBitResidual Bool
    exactReopening :
      (state : FineBitState) →
      reopen sufficientResidual
        (coarseFirstBit state)
        (receipt sufficientResidual state)
      ≡ state
    everyExactResidualHasASeparatedPair :
      ∀ {Receipt : Set} →
      ExactFirstBitResidual Receipt →
      HasSeparatedReceiptPair Receipt

open MinimalBinaryResidualWitness public

canonicalMinimalBinaryResidualWitness : MinimalBinaryResidualWitness
canonicalMinimalBinaryResidualWitness =
  minimalBinaryResidualWitness
    canonicalBoolResidual
    canonicalBinaryResidualReopensExactly
    anyExactResidualMustSeparateAHiddenPair
