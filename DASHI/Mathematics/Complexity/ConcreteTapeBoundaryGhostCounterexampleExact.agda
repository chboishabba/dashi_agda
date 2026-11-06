module DASHI.Mathematics.Complexity.ConcreteTapeBoundaryGhostCounterexampleExact where

------------------------------------------------------------------------
-- SOURCE-NATIVE REFUTATION OF UNCONDITIONAL REVERSE LOCALITY.
--
-- Six aligned cells; single-state, single-symbol machine; right rule.
-- Before: P P P H P P (unique interior old head).
-- After:  H P P P H P (ghost at first cell + legal moved head).
-- Windows:
--   0: P P P -> H P P : right-overlap-plus-two
--   1: P P H -> P P P : right-overlap-minus-one
--   2: P H P -> P P H : legal-centered realizes-right
--   3: H P P -> P H P : right-overlap-plus-one
-- Every window is legal for the SAME original rule; same row length;
-- original interior premise holds; after has TWO heads.
--
-- Therefore localityScanWithInteriorGivesWellFormedStep cannot retain
-- its original unconditional type without a genuine boundary guard.
-- Neither an Agda postulate nor a proof of the false plain lemma
-- is a valid completion. This example is not an NP hardness claim.
-- This integration owner is NOT --safe until the original Local/Pattern/
-- Whole/Character import closure is kernel accepted with safe options.
-- The independent original-carrier finite no-go owner remains separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character

unitEqualSound : ∀ {x y : ⊤} → true ≡ true → x ≡ y
unitEqualSound {tt} {tt} _ = refl

unitEnumeration : Local.FiniteEnumeration ⊤
unitEnumeration = record
  { Local.values = tt ∷ []
  ; Local.occurs = λ _ → ⊤
  ; Local.complete = λ _ → tt
  ; Local.decideEqual = λ _ _ → true
  ; Local.decideEqualRefl = λ _ → refl
  ; Local.decideEqualSound = unitEqualSound
  }

rightRule : Local.TapeRule ⊤ ⊤
rightRule = Local.tape-rule tt tt tt tt Local.moveRight

smallMachine : Local.ConcreteTapeMachine
smallMachine = record
  { Local.State = ⊤
  ; Local.Symbol = ⊤
  ; Local.finiteState = unitEnumeration
  ; Local.finiteSymbol = unitEnumeration
  ; Local.blank = tt
  ; Local.initialState = tt
  ; Local.acceptingState = tt
  ; Local.rules = rightRule ∷ []
  }

P : Local.TapeCell ⊤ ⊤
P = Local.plain tt

H : Local.TapeCell ⊤ ⊤
H = Local.headed tt tt

oldCells : List (Local.TapeCell ⊤ ⊤)
oldCells = P ∷ P ∷ P ∷ H ∷ P ∷ P ∷ []

ghostCells : List (Local.TapeCell ⊤ ⊤)
ghostCells = H ∷ P ∷ P ∷ P ∷ H ∷ P ∷ []

oldRow : Local.TapeRow smallMachine
oldRow = Local.tape-row oldCells

ghostRow : Local.TapeRow smallMachine
ghostRow = Local.tape-row ghostCells

ghostWindowScanLegal :
  Whole.All (Pattern.LegalWindowForRule smallMachine rightRule)
    (Whole.scanWindowsCells smallMachine oldCells ghostCells)
ghostWindowScanLegal =
  Whole.allCons Pattern.right-overlap-plus-two
    (Whole.allCons Pattern.right-overlap-minus-one
      (Whole.allCons (Pattern.legal-centered Local.realizes-right)
        (Whole.allCons Pattern.right-overlap-plus-one Whole.allNil)))

ghostHasValidLocalityScan :
  Character.TransitionLocalityScan smallMachine rightRule oldRow ghostRow
ghostHasValidLocalityScan = record
  { Character.ruleOccursInMachine = Local.ruleHere
  ; Character.sameRowLength = refl
  ; Character.everyWindowLegal = ghostWindowScanLegal
  }

oldHeadIsInterior :
  Character.InteriorHeadConfiguration smallMachine oldRow
oldHeadIsInterior = record
  { Character.prefix = P ∷ P ∷ []
  ; Character.suffix = P ∷ []
  ; Character.leftSymbol = tt
  ; Character.readSymbol = tt
  ; Character.rightSymbol = tt
  ; Character.headState = tt
  ; Character.prefixPlain =
      WF.plainCons (WF.plainCons WF.plainNil)
  ; Character.suffixPlain =
      WF.plainCons WF.plainNil
  ; Character.rowShape = refl
  }

ghostAfterNotUnique :
  WF.ExactlyOneHead ghostCells → ⊥
ghostAfterNotUnique
  (WF.headHere
    (WF.plainCons (WF.plainCons (WF.plainCons ()))))

-- A direct refutation of the *original* claimed consumer type, with
-- both the original semantic scan and original before-interior owner.
unconditionalAfterUniquenessRefuted :
  (∀ {machine rule before after} →
    Character.TransitionLocalityScan machine rule before after →
    Character.InteriorHeadConfiguration machine before →
    WF.ExactlyOneHead (Local.cells after)) →
  ⊥
unconditionalAfterUniquenessRefuted unconditional =
  ghostAfterNotUnique
    (unconditional ghostHasValidLocalityScan oldHeadIsInterior)
