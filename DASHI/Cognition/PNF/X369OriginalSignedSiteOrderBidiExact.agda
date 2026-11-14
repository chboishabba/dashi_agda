module DASHI.Cognition.PNF.X369OriginalSignedSiteOrderBidiExact where

-- X369 A00: original Leech Python PUNCTURE_SITES/SITES signed order,
-- as a NINE-SLOT INDEX CODE for the existing Agda torus; not a second
-- group or a new abstract nine-element carrier.
--
-- Leech models/punctured_nine_wave_prior.py:
-- SITES = ((0,0),(-1,0),(1,0),(0,-1),(0,1),
--          (-1,-1),(1,1),(-1,1),(1,-1)).
-- Original DASHI carrier:
-- DASHI.Physics.Common.FiniteThreeCycleTorusExact.Torus3x3.
-- This file is a source ordering crosswalk; Python source SHA and Agda
-- kernel checker receipts remain separate from the mathematical type.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus
import DASHI.Cognition.PNF.X369OriginalTorusGroupLawExact as Group
import DASHI.Biology.BalancedTernaryFourierModeExact as Fourier
import DASHI.Algebra.TriadicDepthOneCharacters as Characters

-- Slot names are tied to the ORIGINAL Python ordering; they are not
-- asserted to possess an independent algebraic group operation.
data OriginalSourceSlot : Set where
  siteCentre siteMinusZero sitePlusZero
    siteZeroMinus siteZeroPlus
    siteMinusMinus sitePlusPlus
    siteMinusPlus sitePlusMinus : OriginalSourceSlot

sourceSlotOrder : List OriginalSourceSlot
sourceSlotOrder =
  siteCentre ∷ siteMinusZero ∷ sitePlusZero ∷
  siteZeroMinus ∷ siteZeroPlus ∷
  siteMinusMinus ∷ sitePlusPlus ∷
  siteMinusPlus ∷ sitePlusMinus ∷ []

sourceSlotIndex : OriginalSourceSlot → Nat
sourceSlotIndex siteCentre = 0
sourceSlotIndex siteMinusZero = 1
sourceSlotIndex sitePlusZero = 2
sourceSlotIndex siteZeroMinus = 3
sourceSlotIndex siteZeroPlus = 4
sourceSlotIndex siteMinusMinus = 5
sourceSlotIndex sitePlusPlus = 6
sourceSlotIndex siteMinusPlus = 7
sourceSlotIndex sitePlusMinus = 8

sourceToOriginalTorus : OriginalSourceSlot → Torus.Torus3x3
sourceToOriginalTorus siteCentre =
  Torus.torusPoint Torus.residueZero Torus.residueZero
sourceToOriginalTorus siteMinusZero =
  Torus.torusPoint Torus.residueMinus Torus.residueZero
sourceToOriginalTorus sitePlusZero =
  Torus.torusPoint Torus.residuePlus Torus.residueZero
sourceToOriginalTorus siteZeroMinus =
  Torus.torusPoint Torus.residueZero Torus.residueMinus
sourceToOriginalTorus siteZeroPlus =
  Torus.torusPoint Torus.residueZero Torus.residuePlus
sourceToOriginalTorus siteMinusMinus =
  Torus.torusPoint Torus.residueMinus Torus.residueMinus
sourceToOriginalTorus sitePlusPlus =
  Torus.torusPoint Torus.residuePlus Torus.residuePlus
sourceToOriginalTorus siteMinusPlus =
  Torus.torusPoint Torus.residueMinus Torus.residuePlus
sourceToOriginalTorus sitePlusMinus =
  Torus.torusPoint Torus.residuePlus Torus.residueMinus

originalTorusToSource : Torus.Torus3x3 → OriginalSourceSlot
originalTorusToSource (Torus.torusPoint Torus.residueZero Torus.residueZero) =
  siteCentre
originalTorusToSource (Torus.torusPoint Torus.residueMinus Torus.residueZero) =
  siteMinusZero
originalTorusToSource (Torus.torusPoint Torus.residuePlus Torus.residueZero) =
  sitePlusZero
originalTorusToSource (Torus.torusPoint Torus.residueZero Torus.residueMinus) =
  siteZeroMinus
originalTorusToSource (Torus.torusPoint Torus.residueZero Torus.residuePlus) =
  siteZeroPlus
originalTorusToSource (Torus.torusPoint Torus.residueMinus Torus.residueMinus) =
  siteMinusMinus
originalTorusToSource (Torus.torusPoint Torus.residuePlus Torus.residuePlus) =
  sitePlusPlus
originalTorusToSource (Torus.torusPoint Torus.residueMinus Torus.residuePlus) =
  siteMinusPlus
originalTorusToSource (Torus.torusPoint Torus.residuePlus Torus.residueMinus) =
  sitePlusMinus

sourceSlotRoundTrip : (slot : OriginalSourceSlot) →
  originalTorusToSource (sourceToOriginalTorus slot) ≡ slot
sourceSlotRoundTrip siteCentre = refl
sourceSlotRoundTrip siteMinusZero = refl
sourceSlotRoundTrip sitePlusZero = refl
sourceSlotRoundTrip siteZeroMinus = refl
sourceSlotRoundTrip siteZeroPlus = refl
sourceSlotRoundTrip siteMinusMinus = refl
sourceSlotRoundTrip sitePlusPlus = refl
sourceSlotRoundTrip siteMinusPlus = refl
sourceSlotRoundTrip sitePlusMinus = refl

originalTorusPointRoundTrip : (point : Torus.Torus3x3) →
  sourceToOriginalTorus (originalTorusToSource point) ≡ point
originalTorusPointRoundTrip
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalTorusPointRoundTrip
  (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalTorusPointRoundTrip
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalTorusPointRoundTrip
  (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalTorusPointRoundTrip
  (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalTorusPointRoundTrip
  (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalTorusPointRoundTrip
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalTorusPointRoundTrip
  (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalTorusPointRoundTrip
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl

-- Translate source SLOTS only by transport through the ORIGINAL group.
sourceSlotTranslateFirst : OriginalSourceSlot → OriginalSourceSlot
sourceSlotTranslateFirst slot =
  originalTorusToSource (Group.originalTorusAdd
    (sourceToOriginalTorus slot) Group.originalTorusFirstGenerator)

sourceSlotTranslateSecond : OriginalSourceSlot → OriginalSourceSlot
sourceSlotTranslateSecond slot =
  originalTorusToSource (Group.originalTorusAdd
    (sourceToOriginalTorus slot) Group.originalTorusSecondGenerator)

sourceFirstTranslationOriginalWeld : (slot : OriginalSourceSlot) →
  sourceToOriginalTorus (sourceSlotTranslateFirst slot)
  ≡ Torus.translateFirst (sourceToOriginalTorus slot)
sourceFirstTranslationOriginalWeld slot
  rewrite originalTorusPointRoundTrip
    (Group.originalTorusAdd
      (sourceToOriginalTorus slot) Group.originalTorusFirstGenerator) =
  Group.firstGeneratorIsOriginalTranslation (sourceToOriginalTorus slot)

sourceSecondTranslationOriginalWeld : (slot : OriginalSourceSlot) →
  sourceToOriginalTorus (sourceSlotTranslateSecond slot)
  ≡ Torus.translateSecond (sourceToOriginalTorus slot)
sourceSecondTranslationOriginalWeld slot
  rewrite originalTorusPointRoundTrip
    (Group.originalTorusAdd
      (sourceToOriginalTorus slot) Group.originalTorusSecondGenerator) =
  Group.secondGeneratorIsOriginalTranslation (sourceToOriginalTorus slot)

-- A sign/orientation receipt: the source positive first generator
-- evaluates the ORIGINAL character omega, not its conjugate.
sourceFirstGeneratorCharacterIsOmega :
  Characters.multiplyPhase
    (Fourier.firstCharacter
      (sourceToOriginalTorus sitePlusZero)
      (sourceToOriginalTorus sitePlusZero))
    (Fourier.secondCharacter
      (sourceToOriginalTorus sitePlusZero)
      (sourceToOriginalTorus sitePlusZero))
  ≡ Characters.phase1
sourceFirstGeneratorCharacterIsOmega = refl

sourceNegativeGeneratorCharacterIsConjugate :
  Fourier.firstCharacter (sourceToOriginalTorus sitePlusZero)
                         (sourceToOriginalTorus siteMinusZero)
  ≡ Characters.phase2
sourceNegativeGeneratorCharacterIsConjugate = refl

-- Still to be checked in Agda: selected original imports and kernel.
-- A03/A04 full Fourier sum identities, A05 real four-pair basis and
-- original checkpoint input/output consumer transport remain OPEN.
