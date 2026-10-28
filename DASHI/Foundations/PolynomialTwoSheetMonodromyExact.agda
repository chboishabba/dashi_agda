module DASHI.Foundations.PolynomialTwoSheetMonodromyExact where

------------------------------------------------------------------------
-- FINITE TWO-SHEET MONODROMY MODEL
-- Riemann (1851) and the standard square-root covering of C*.
--
-- This module proves that a single loop acting as a sheet swap prevents a
-- monodromy-invariant CHOICE OF SHEET. It is an exact finite shadow of the
-- global continuous square-root section obstruction, not a topology theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

data Sheet2 : Set where
  upperSheet lowerSheet : Sheet2

deckSwap : Sheet2 → Sheet2
deckSwap upperSheet = lowerSheet
deckSwap lowerSheet = upperSheet

deckSwapInvolution : (s : Sheet2) →
  deckSwap (deckSwap s) ≡ s
deckSwapInvolution upperSheet = refl
deckSwapInvolution lowerSheet = refl

coarseCoefficient : Sheet2 → ⊤
coarseCoefficient _ = tt

sameCoefficientAfterDeckLoop : (s : Sheet2) →
  coarseCoefficient (deckSwap s) ≡ coarseCoefficient s
sameCoefficientAfterDeckLoop upperSheet = refl
sameCoefficientAfterDeckLoop lowerSheet = refl

deckSwapHasNoFixedSheet :
  (s : Sheet2) → deckSwap s ≡ s → ⊥
deckSwapHasNoFixedSheet upperSheet ()
deckSwapHasNoFixedSheet lowerSheet ()

-- This is the finite obstruction: an equivariant section cannot choose
-- a fixed sheet at the distinguished coefficient basepoint.
record MonodromyInvariantSheetSelection : Set where
  constructor monodromy-invariant-sheet-selection
  field
    sheet : Sheet2
    invariantUnderGenerator : deckSwap sheet ≡ sheet
open MonodromyInvariantSheetSelection public

noMonodromyInvariantSelection :
  MonodromyInvariantSheetSelection → ⊥
noMonodromyInvariantSelection choice =
  deckSwapHasNoFixedSheet (sheet choice)
    (invariantUnderGenerator choice)

data C2LoopParity : Set where
  evenLoop oddLoop : C2LoopParity

loopAction : C2LoopParity → Sheet2 → Sheet2
loopAction evenLoop s = s
loopAction oddLoop s = deckSwap s

composeParity : C2LoopParity → C2LoopParity → C2LoopParity
composeParity evenLoop p = p
composeParity oddLoop evenLoop = oddLoop
composeParity oddLoop oddLoop = evenLoop

loopActionComposition :
  (a b : C2LoopParity) (s : Sheet2) →
  loopAction (composeParity a b) s
  ≡ loopAction a (loopAction b s)
loopActionComposition evenLoop evenLoop upperSheet = refl
loopActionComposition evenLoop evenLoop lowerSheet = refl
loopActionComposition evenLoop oddLoop upperSheet = refl
loopActionComposition evenLoop oddLoop lowerSheet = refl
loopActionComposition oddLoop evenLoop upperSheet = refl
loopActionComposition oddLoop evenLoop lowerSheet = refl
loopActionComposition oddLoop oddLoop upperSheet = refl
loopActionComposition oddLoop oddLoop lowerSheet = refl

-- Actual complex sqrt(w) branch lifting would require an explicit
-- C* continuous path/covering authority, separate from this finite model.
