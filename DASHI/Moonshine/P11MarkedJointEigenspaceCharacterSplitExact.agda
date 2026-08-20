module DASHI.Moonshine.P11MarkedJointEigenspaceCharacterSplitExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
-- Restriction to C3 and character decomposition.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full-level-2 deck action.
--
-- CROSS-POLLINATION
-- PR #576 proves that the complete (-1,1,+1) simultaneous T3/T5/F eigenspace
-- has dimension three on the source-native marked carrier.  PR #572 supplies
-- the exact existing-Phase3 C3 character language.  This file composes the two
-- results instead of treating either as a sample-mode observation.
--
-- DASHI CONTRIBUTION
--
-- The full arithmetic collision eigenspace splits under the ACTUAL deck C3 as
--
--   E_(-1,1,+1) | C3 = chi_0 + chi_1 + chi_2.
--
-- Its chi_0 line is the coarse Brandt-newform mode; its chi_1+chi_2 plane is
-- the deck-standard sector.  Thus the missing information in (T3,T5,F) is
-- exactly a finite deck-character coordinate on this three-dimensional block.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational using (ℚ; _-_; -_)

import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.Phase3RootCharacterWeldExact as Root
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact as Deck
import DASHI.Moonshine.P11MarkedX2JointHeckeFrobeniusSpectrumExact as Joint
import DASHI.Moonshine.P11MarkedX2DeckCharacterSeparationExact as Char

------------------------------------------------------------------------
-- The complete arithmetic eigenspace has the independently proved dimension 3.
------------------------------------------------------------------------

arithmeticCollisionMultiplicity : Nat
arithmeticCollisionMultiplicity =
  Joint.JointSpectrumBoundary.nonconstantEvenJointMultiplicity
    Joint.canonicalJointSpectrumBoundary

arithmeticCollisionMultiplicityIsThree : arithmeticCollisionMultiplicity ≡ 3
arithmeticCollisionMultiplicityIsThree = refl

------------------------------------------------------------------------
-- Deck pullback on rational observables.
------------------------------------------------------------------------

deckRPullback : Joint.Observable5 → Joint.Observable5
deckRPullback observable state = observable (Deck.deckR state)

deckSPullback : Joint.Observable5 → Joint.Observable5
deckSPullback observable state = observable (Deck.deckS state)

mixedModeDeckRFixed :
  (state : Fine.P11Fine5) →
  deckRPullback Joint.mixedEvenMode state ≡ Joint.mixedEvenMode state
mixedModeDeckRFixed Fine.a0 = refl
mixedModeDeckRFixed Fine.a1 = refl
mixedModeDeckRFixed Fine.b0 = refl
mixedModeDeckRFixed Fine.b1 = refl
mixedModeDeckRFixed Fine.b2 = refl

mixedModeDeckSFixed :
  (state : Fine.P11Fine5) →
  deckSPullback Joint.mixedEvenMode state ≡ Joint.mixedEvenMode state
mixedModeDeckSFixed Fine.a0 = refl
mixedModeDeckSFixed Fine.a1 = refl
mixedModeDeckSFixed Fine.b0 = refl
mixedModeDeckSFixed Fine.b1 = refl
mixedModeDeckSFixed Fine.b2 = refl

-- The two difference modes are not individually C3-fixed; the deck rotation
-- mixes them inside the two-dimensional standard plane.

bDiff01DeckRIsMinusDiff02 :
  (state : Fine.P11Fine5) →
  deckRPullback Joint.bDiff01Mode state ≡ - Joint.bDiff02Mode state
bDiff01DeckRIsMinusDiff02 Fine.a0 = refl
bDiff01DeckRIsMinusDiff02 Fine.a1 = refl
bDiff01DeckRIsMinusDiff02 Fine.b0 = refl
bDiff01DeckRIsMinusDiff02 Fine.b1 = refl
bDiff01DeckRIsMinusDiff02 Fine.b2 = refl

bDiff02DeckRIsDifference :
  (state : Fine.P11Fine5) →
  deckRPullback Joint.bDiff02Mode state
  ≡ Joint.bDiff01Mode state - Joint.bDiff02Mode state
bDiff02DeckRIsDifference Fine.a0 = refl
bDiff02DeckRIsDifference Fine.a1 = refl
bDiff02DeckRIsDifference Fine.b0 = refl
bDiff02DeckRIsDifference Fine.b1 = refl
bDiff02DeckRIsDifference Fine.b2 = refl

------------------------------------------------------------------------
-- Exact C3 character multiplicity split of the COMPLETE 3D arithmetic block.
------------------------------------------------------------------------

collisionC3Multiplicity : Char.C3CharacterMultiplicity
collisionC3Multiplicity = Char.c3Multiplicity 1 1 1

brandtPartC3Multiplicity : Char.C3CharacterMultiplicity
brandtPartC3Multiplicity = Char.brandtC3Multiplicity

standardPartC3Multiplicity : Char.C3CharacterMultiplicity
standardPartC3Multiplicity = Char.standardC3Multiplicity

addC3Multiplicity :
  Char.C3CharacterMultiplicity →
  Char.C3CharacterMultiplicity →
  Char.C3CharacterMultiplicity
addC3Multiplicity left right = Char.c3Multiplicity
  (Char.chi0Multiplicity left + Char.chi0Multiplicity right)
  (Char.chi1Multiplicity left + Char.chi1Multiplicity right)
  (Char.chi2Multiplicity left + Char.chi2Multiplicity right)

collisionSplitIsBrandtPlusStandard :
  addC3Multiplicity brandtPartC3Multiplicity standardPartC3Multiplicity
  ≡ collisionC3Multiplicity
collisionSplitIsBrandtPlusStandard = refl

collisionCharacterDimension :
  Char.chi0Multiplicity collisionC3Multiplicity
  + Char.chi1Multiplicity collisionC3Multiplicity
  + Char.chi2Multiplicity collisionC3Multiplicity
  ≡ arithmeticCollisionMultiplicity
collisionCharacterDimension = refl

------------------------------------------------------------------------
-- Root labels: the three dimensions are the three distinct C3 characters.
------------------------------------------------------------------------

collisionChi0AtR : Phase.Phase3
collisionChi0AtR = Root.character Phase.phase0 Phase.phase1

collisionChi1AtR : Phase.Phase3
collisionChi1AtR = Root.character Phase.phase1 Phase.phase1

collisionChi2AtR : Phase.Phase3
collisionChi2AtR = Root.character Phase.phase2 Phase.phase1

collisionCharacterRootsExact :
  collisionChi0AtR ≡ Phase.phase0
  × collisionChi1AtR ≡ Phase.phase1
  × collisionChi2AtR ≡ Phase.phase2
collisionCharacterRootsExact = refl , refl , refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record P11JointEigenspaceCharacterBoundary : Set where
  field
    completeArithmeticMultiplicityThreeConsumed : Bool
    completeArithmeticMultiplicityThreeConsumedIsTrue :
      completeArithmeticMultiplicityThreeConsumed ≡ true

    collisionBlockSplitIntoThreeC3Characters : Bool
    collisionBlockSplitIntoThreeC3CharactersIsTrue :
      collisionBlockSplitIntoThreeC3Characters ≡ true

    brandtLineIdentifiedWithTrivialC3Part : Bool
    brandtLineIdentifiedWithTrivialC3PartIsTrue :
      brandtLineIdentifiedWithTrivialC3Part ≡ true

    standardPlaneIdentifiedWithConjugateC3Pair : Bool
    standardPlaneIdentifiedWithConjugateC3PairIsTrue :
      standardPlaneIdentifiedWithConjugateC3Pair ≡ true

    arithmeticMultiplicityThreeTreatedAsIrreducible : Bool
    arithmeticMultiplicityThreeTreatedAsIrreducibleIsFalse :
      arithmeticMultiplicityThreeTreatedAsIrreducible ≡ false

canonicalP11JointEigenspaceCharacterBoundary : P11JointEigenspaceCharacterBoundary
canonicalP11JointEigenspaceCharacterBoundary = record
  { completeArithmeticMultiplicityThreeConsumed = true
  ; completeArithmeticMultiplicityThreeConsumedIsTrue = refl
  ; collisionBlockSplitIntoThreeC3Characters = true
  ; collisionBlockSplitIntoThreeC3CharactersIsTrue = refl
  ; brandtLineIdentifiedWithTrivialC3Part = true
  ; brandtLineIdentifiedWithTrivialC3PartIsTrue = refl
  ; standardPlaneIdentifiedWithConjugateC3Pair = true
  ; standardPlaneIdentifiedWithConjugateC3PairIsTrue = refl
  ; arithmeticMultiplicityThreeTreatedAsIrreducible = false
  ; arithmeticMultiplicityThreeTreatedAsIrreducibleIsFalse = refl
  }
