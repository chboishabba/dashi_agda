module DASHI.Physics.Plasma.ElsasserSectorSelectionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.HelicityElsasserBinaryAxesExact as Axes

------------------------------------------------------------------------
-- ELSASSER SECTOR SELECTION
--
-- The exact amplitude identities show that only mixed Elsasser products
-- survive.  This module records that selection independently of helical sign.
------------------------------------------------------------------------

data OrderedElsasserPair : Set where
  plusPlus
  plusMinus
  minusPlus
  minusMinus
  : OrderedElsasserPair

pairOf : Axes.ElsasserOrientation → Axes.ElsasserOrientation → OrderedElsasserPair
pairOf Axes.elsasserPlus Axes.elsasserPlus = plusPlus
pairOf Axes.elsasserPlus Axes.elsasserMinus = plusMinus
pairOf Axes.elsasserMinus Axes.elsasserPlus = minusPlus
pairOf Axes.elsasserMinus Axes.elsasserMinus = minusMinus

data SurvivesElsasserAmplitude : OrderedElsasserPair → Set where
  plusMinusSurvives : SurvivesElsasserAmplitude plusMinus
  minusPlusSurvives : SurvivesElsasserAmplitude minusPlus

sameSignPlusExcluded : SurvivesElsasserAmplitude plusPlus → ⊥
sameSignPlusExcluded ()

sameSignMinusExcluded : SurvivesElsasserAmplitude minusMinus → ⊥
sameSignMinusExcluded ()

record SectorSelectionReceipt : Set where
  constructor sector-selection-receipt
  field
    advectingOrientation : Axes.ElsasserOrientation
    advectedOrientation : Axes.ElsasserOrientation
    selectedPair : OrderedElsasserPair
    pairIsLiteral : selectedPair ≡ pairOf advectingOrientation advectedOrientation
    survivesAmplitudeAlgebra : SurvivesElsasserAmplitude selectedPair
    receiptReference : String

open SectorSelectionReceipt public

record SectorSelectionBoundary : Set where
  constructor sector-selection-boundary
  field
    plusPlusNonlinearAmplitudeSurvives : Bool
    plusPlusNonlinearAmplitudeSurvivesIsFalse :
      plusPlusNonlinearAmplitudeSurvives ≡ false

    minusMinusNonlinearAmplitudeSurvives : Bool
    minusMinusNonlinearAmplitudeSurvivesIsFalse :
      minusMinusNonlinearAmplitudeSurvives ≡ false

    plusMinusAndMinusPlusBothSurvive : Bool
    plusMinusAndMinusPlusBothSurviveIsTrue :
      plusMinusAndMinusPlusBothSurvive ≡ true

    helicitySignDeterminesElsasserSelection : Bool
    helicitySignDeterminesElsasserSelectionIsFalse :
      helicitySignDeterminesElsasserSelection ≡ false

canonicalSectorSelectionBoundary : SectorSelectionBoundary
canonicalSectorSelectionBoundary =
  sector-selection-boundary false refl false refl true refl false refl
