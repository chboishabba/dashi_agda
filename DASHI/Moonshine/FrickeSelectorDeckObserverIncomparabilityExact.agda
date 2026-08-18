module DASHI.Moonshine.FrickeSelectorDeckObserverIncomparabilityExact where

------------------------------------------------------------------------
-- COARSE FRICKE SELECTOR vs MARKED DECK-REPRESENTATION OBSERVER
--
-- PRIMARY CONTEXT
--
-- Andrew P. Ogg, "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7.
-- MR 417184; no DOI asserted.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- The table-free Fricke/Ogg lane and the marked deck-isotypic lane observe
-- DIFFERENT information.  This file proves exact non-factorability in BOTH
-- directions on source-native p11/p37 witnesses.
--
-- 1. deck type cannot determine the coarse Frobenius selector:
--      p11 has a genuine standard-deck sector;
--      p37 has a genuine standard-deck sector;
--      but the coarse Frobenius paired-orbit defects are 0 and 1.
--
-- 2. coarse selector cannot determine deck type:
--      at p37 the prime-level coarse defect is one;
--      the actual marked Hecke system contains BOTH a deck-trivial mode and a
--      deck-standard mode with the same scalar (T3,T5,F)=(1,0,+1).
--
-- Hence neither coordinate is a refinement of the other.  A consumer needing
-- both Ogg/Fricke status and marked representation identity must retain the
-- product observer.  The deck coordinate is not an Ogg selector, and the Ogg
-- selector is not a decoder for marked multiplicity/representation data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as P11
import DASHI.Moonshine.P37MarkedDeckIsotypicCollisionExact as P37
import DASHI.Moonshine.P11P37MarkedDeckSelectorCutsetExact as Cutset

------------------------------------------------------------------------
-- Shared deck-type vocabulary for the two exact marked systems.
------------------------------------------------------------------------

data SharedDeckType : Set where
  deckTrivial deckSign deckStandard : SharedDeckType

-- Proof-relevant witnesses that the standard sector is actually present on
-- each source-native marked system, rather than merely being a label.

p11StandardWitness : P11.Int5
p11StandardWitness = P11.standardVector1

p37StandardWitness : P37.Iso.StdBlock3
p37StandardWitness = P37.p37StandardCollisionVector

p37TrivialWitness : P37.Iso.Block3
p37TrivialWitness = P37.p37TrivialCollisionVector

------------------------------------------------------------------------
-- Direction 1: deck type cannot determine coarse selector status.
------------------------------------------------------------------------

data PrimeControl : Set where
  control11 control37 : PrimeControl

deckObservation : PrimeControl → SharedDeckType
deckObservation control11 = deckStandard
deckObservation control37 = deckStandard

coarseSelectorObservation : PrimeControl → Nat
coarseSelectorObservation control11 = Cutset.p11CoarseFrobeniusPairDefect
coarseSelectorObservation control37 = Cutset.p37CoarseFrobeniusPairDefect

sameDeckTypeAcrossControls :
  deckObservation control11 ≡ deckObservation control37
sameDeckTypeAcrossControls = refl

coarseSelectorDiffersAcrossControls :
  coarseSelectorObservation control11 ≡ coarseSelectorObservation control37 → ⊥
coarseSelectorDiffersAcrossControls =
  Cutset.coarseFrobeniusPairDefectSeparates11And37

DeckDeterminesSelector : Set
DeckDeterminesSelector =
  Σ (SharedDeckType → Nat)
    (λ decode → (x : PrimeControl) → decode (deckObservation x) ≡ coarseSelectorObservation x)

deckCannotDetermineCoarseSelector : DeckDeterminesSelector → ⊥
deckCannotDetermineCoarseSelector (decode , factors) =
  coarseSelectorDiffersAcrossControls
    (trans
      (sym (factors control11))
      (trans
        (cong decode sameDeckTypeAcrossControls)
        (factors control37)))

------------------------------------------------------------------------
-- Direction 2: coarse selector cannot determine marked deck type.
------------------------------------------------------------------------

data P37Mode : Set where
  p37TrivialMode p37StandardMode : P37Mode

p37ModeDeckObservation : P37Mode → SharedDeckType
p37ModeDeckObservation p37TrivialMode = deckTrivial
p37ModeDeckObservation p37StandardMode = deckStandard

p37ModeCoarseSelector : P37Mode → Nat
p37ModeCoarseSelector p37TrivialMode = Cutset.p37CoarseFrobeniusPairDefect
p37ModeCoarseSelector p37StandardMode = Cutset.p37CoarseFrobeniusPairDefect

p37ModesShareCoarseSelector :
  p37ModeCoarseSelector p37TrivialMode ≡ p37ModeCoarseSelector p37StandardMode
p37ModesShareCoarseSelector = refl

p37ModesHaveDifferentDeckType :
  p37ModeDeckObservation p37TrivialMode
  ≡ p37ModeDeckObservation p37StandardMode → ⊥
p37ModesHaveDifferentDeckType ()

SelectorDeterminesDeck : Set
SelectorDeterminesDeck =
  Σ (Nat → SharedDeckType)
    (λ decode → (x : P37Mode) → decode (p37ModeCoarseSelector x) ≡ p37ModeDeckObservation x)

coarseSelectorCannotDetermineDeck : SelectorDeterminesDeck → ⊥
coarseSelectorCannotDetermineDeck (decode , factors) =
  p37ModesHaveDifferentDeckType
    (trans
      (sym (factors p37TrivialMode))
      (trans
        (cong decode p37ModesShareCoarseSelector)
        (factors p37StandardMode)))

------------------------------------------------------------------------
-- Product observer: retain both roles instead of forcing one through the other.
------------------------------------------------------------------------

record SelectorDeckObservation : Set where
  constructor selectorDeck
  field
    coarseDefect : Nat
    deckType : SharedDeckType
open SelectorDeckObservation public

p37CombinedObservation : P37Mode → SelectorDeckObservation
p37CombinedObservation x =
  selectorDeck (p37ModeCoarseSelector x) (p37ModeDeckObservation x)

combinedSeparatesP37Modes :
  p37CombinedObservation p37TrivialMode
  ≡ p37CombinedObservation p37StandardMode → ⊥
combinedSeparatesP37Modes ()

record FrickeSelectorDeckObserverIncomparabilityBoundary : Set where
  field
    p11StandardDeckWitnessPresent : Bool
    p37StandardDeckWitnessPresent : Bool
    p37TrivialDeckWitnessPresent : Bool
    sameDeckTypeCanHaveDifferentCoarseSelector : Bool
    sameCoarseSelectorCanHaveDifferentDeckType : Bool
    deckDeterminesCoarseSelector : Bool
    coarseSelectorDeterminesDeck : Bool
    productObserverRetainsBothRoles : Bool
    finiteMonsterPrimeLaneTableUsed : Bool

canonicalFrickeSelectorDeckObserverIncomparabilityBoundary :
  FrickeSelectorDeckObserverIncomparabilityBoundary
canonicalFrickeSelectorDeckObserverIncomparabilityBoundary = record
  { p11StandardDeckWitnessPresent = true
  ; p37StandardDeckWitnessPresent = true
  ; p37TrivialDeckWitnessPresent = true
  ; sameDeckTypeCanHaveDifferentCoarseSelector = true
  ; sameCoarseSelectorCanHaveDifferentDeckType = true
  ; deckDeterminesCoarseSelector = false
  ; coarseSelectorDeterminesDeck = false
  ; productObserverRetainsBothRoles = true
  ; finiteMonsterPrimeLaneTableUsed = false
  }
