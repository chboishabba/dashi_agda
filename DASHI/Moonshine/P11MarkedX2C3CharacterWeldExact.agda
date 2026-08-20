module DASHI.Moonshine.P11MarkedX2C3CharacterWeldExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer. DOI: 10.1007/978-1-4684-9458-7.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton, 1985.
-- DOI: 10.1515/9781400881710.
--
-- DASHI CONTRIBUTION
--
-- Identify the exact place where the Phase3/C3 character weld belongs in the
-- source-native full-level-2 p=11 geometry.
--
-- The naive C3 action on ell=2 EDGE SLOTS at fixed source was falsified in
-- P11T2TernarySlotCharacterNoGoExact.  By contrast, the genuine right deck
-- action on the three-sheet j=1728 fibre is literally
--
--   b0 -> b1 -> b2 -> b0,
--
-- and deck reflection fixes b0 while swapping b1,b2.  Under
--
--   b0 <-> phase0, b1 <-> phase1, b2 <-> phase2,
--
-- these are exactly zeta rotation and inversion/conjugation from
-- Phase3RootCharacterWeldExact.  Hence the three C3 character rows provide the
-- correct finite harmonic coordinates for the deck-C3 subgroup.
--
-- The two-sheet j=0 fibre behaves differently: deckR is trivial and deckS
-- swaps the two sheets, supplying the sign-like C2 sector.  No identification
-- is made between the B-fibre C3 characters and the coarse Brandt carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.Phase3RootCharacterWeldExact as Root3
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact as Deck

------------------------------------------------------------------------
-- Three-sheet B fibre and its exact Phase3 chart.
------------------------------------------------------------------------

data BDeckFibre : Set where
  bF0 bF1 bF2 : BDeckFibre

embedB : BDeckFibre → Fine.P11Fine5
embedB bF0 = Fine.b0
embedB bF1 = Fine.b1
embedB bF2 = Fine.b2

bPhase : BDeckFibre → Phase.Phase3
bPhase bF0 = Phase.phase0
bPhase bF1 = Phase.phase1
bPhase bF2 = Phase.phase2

phaseB : Phase.Phase3 → BDeckFibre
phaseB Phase.phase0 = bF0
phaseB Phase.phase1 = bF1
phaseB Phase.phase2 = bF2

bPhaseRoundTrip : (b : BDeckFibre) → phaseB (bPhase b) ≡ b
bPhaseRoundTrip bF0 = refl
bPhaseRoundTrip bF1 = refl
bPhaseRoundTrip bF2 = refl

phaseBRoundTrip : (p : Phase.Phase3) → bPhase (phaseB p) ≡ p
phaseBRoundTrip Phase.phase0 = refl
phaseBRoundTrip Phase.phase1 = refl
phaseBRoundTrip Phase.phase2 = refl

bRotate : BDeckFibre → BDeckFibre
bRotate bF0 = bF1
bRotate bF1 = bF2
bRotate bF2 = bF0

bReflect : BDeckFibre → BDeckFibre
bReflect bF0 = bF0
bReflect bF1 = bF2
bReflect bF2 = bF1

bRotationIsDeckR :
  (b : BDeckFibre) → embedB (bRotate b) ≡ Deck.deckR (embedB b)
bRotationIsDeckR bF0 = refl
bRotationIsDeckR bF1 = refl
bRotationIsDeckR bF2 = refl

bReflectionIsDeckS :
  (b : BDeckFibre) → embedB (bReflect b) ≡ Deck.deckS (embedB b)
bReflectionIsDeckS bF0 = refl
bReflectionIsDeckS bF1 = refl
bReflectionIsDeckS bF2 = refl

bRotationIsZetaRotation :
  (b : BDeckFibre) →
  bPhase (bRotate b) ≡ Root3.zetaRotate (bPhase b)
bRotationIsZetaRotation bF0 = refl
bRotationIsZetaRotation bF1 = refl
bRotationIsZetaRotation bF2 = refl

bReflectionIsPhaseInverse :
  (b : BDeckFibre) →
  bPhase (bReflect b) ≡ Root3.phaseInverse (bPhase b)
bReflectionIsPhaseInverse bF0 = refl
bReflectionIsPhaseInverse bF1 = refl
bReflectionIsPhaseInverse bF2 = refl

bDeckDihedralRelation :
  (b : BDeckFibre) →
  bReflect (bRotate (bReflect b)) ≡ bRotate (bRotate b)
bDeckDihedralRelation bF0 = refl
bDeckDihedralRelation bF1 = refl
bDeckDihedralRelation bF2 = refl

------------------------------------------------------------------------
-- Exact C3 character coordinates on the genuine deck rotation.
------------------------------------------------------------------------

bDeckCharacter : Phase.Phase3 → BDeckFibre → Phase.Phase3
bDeckCharacter k b = Root3.character k (bPhase b)

bDeckCharacterDiagonalizesRotation :
  (k : Phase.Phase3) → (b : BDeckFibre) →
  bDeckCharacter k (bRotate b)
  ≡ Root3.phaseMul k (bDeckCharacter k b)
bDeckCharacterDiagonalizesRotation Phase.phase0 bF0 = refl
bDeckCharacterDiagonalizesRotation Phase.phase0 bF1 = refl
bDeckCharacterDiagonalizesRotation Phase.phase0 bF2 = refl
bDeckCharacterDiagonalizesRotation Phase.phase1 bF0 = refl
bDeckCharacterDiagonalizesRotation Phase.phase1 bF1 = refl
bDeckCharacterDiagonalizesRotation Phase.phase1 bF2 = refl
bDeckCharacterDiagonalizesRotation Phase.phase2 bF0 = refl
bDeckCharacterDiagonalizesRotation Phase.phase2 bF1 = refl
bDeckCharacterDiagonalizesRotation Phase.phase2 bF2 = refl

------------------------------------------------------------------------
-- Separate two-sheet A fibre: rotation trivial, reflection swaps sheets.
------------------------------------------------------------------------

data ADeckFibre : Set where
  aF0 aF1 : ADeckFibre

embedA : ADeckFibre → Fine.P11Fine5
embedA aF0 = Fine.a0
embedA aF1 = Fine.a1

aRotate : ADeckFibre → ADeckFibre
aRotate aF0 = aF0
aRotate aF1 = aF1

aReflect : ADeckFibre → ADeckFibre
aReflect aF0 = aF1
aReflect aF1 = aF0

aRotationIsDeckR :
  (a : ADeckFibre) → embedA (aRotate a) ≡ Deck.deckR (embedA a)
aRotationIsDeckR aF0 = refl
aRotationIsDeckR aF1 = refl

aReflectionIsDeckS :
  (a : ADeckFibre) → embedA (aReflect a) ≡ Deck.deckS (embedA a)
aReflectionIsDeckS aF0 = refl
aReflectionIsDeckS aF1 = refl

record P11MarkedX2C3CharacterBoundary : Set where
  field
    genuineDeckC3PhaseChartConstructed : Bool
    genuineDeckC3PhaseChartConstructedIsTrue :
      genuineDeckC3PhaseChartConstructed ≡ true

    deckReflectionMatchesPhaseConjugation : Bool
    deckReflectionMatchesPhaseConjugationIsTrue :
      deckReflectionMatchesPhaseConjugation ≡ true

    c3CharactersDiagonalizeGenuineDeckRotation : Bool
    c3CharactersDiagonalizeGenuineDeckRotationIsTrue :
      c3CharactersDiagonalizeGenuineDeckRotation ≡ true

    aFibreSeparatedAsC2Sector : Bool
    aFibreSeparatedAsC2SectorIsTrue : aFibreSeparatedAsC2Sector ≡ true

    edgeSlotC3NoGoOverridden : Bool
    edgeSlotC3NoGoOverriddenIsFalse : edgeSlotC3NoGoOverridden ≡ false

canonicalP11MarkedX2C3CharacterBoundary : P11MarkedX2C3CharacterBoundary
canonicalP11MarkedX2C3CharacterBoundary = record
  { genuineDeckC3PhaseChartConstructed = true
  ; genuineDeckC3PhaseChartConstructedIsTrue = refl
  ; deckReflectionMatchesPhaseConjugation = true
  ; deckReflectionMatchesPhaseConjugationIsTrue = refl
  ; c3CharactersDiagonalizeGenuineDeckRotation = true
  ; c3CharactersDiagonalizeGenuineDeckRotationIsTrue = refl
  ; aFibreSeparatedAsC2Sector = true
  ; aFibreSeparatedAsC2SectorIsTrue = refl
  ; edgeSlotC3NoGoOverridden = false
  ; edgeSlotC3NoGoOverriddenIsFalse = refl
  }
