module DASHI.Cognition.PNF.X369OriginalPointedEightSlotBidiExact where

-- A05: explicit original LEEC H eight-puncture + independent centre,
-- using the original signed Python slot crosswalk A00 and original
-- FiniteThreeCycleTorusExact carrier. This is the POINTED spatial
-- representation, not yet the four real Fourier conjugate pairs.
--
-- No new nine-element torus is declared. All algebraic hypotheses are
-- explicit; the real / Eisenstein instantiation and a postulate-free
-- kernel acceptance receipt remain separate.

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus
import DASHI.Cognition.PNF.X369OriginalSignedSiteOrderBidiExact as Sites

record OriginalPuncturedEight (A : Set) : Set where
  constructor puncturedEight
  field
    minusZero plusZero zeroMinus zeroPlus
      minusMinus plusPlus minusPlus plusMinus : A

open OriginalPuncturedEight public

originalEightSlotRead : {A : Set} → A → OriginalPuncturedEight A →
                        Sites.OriginalSourceSlot → A
originalEightSlotRead centreOffset e Sites.siteCentre = centreOffset
originalEightSlotRead centreOffset e Sites.siteMinusZero = minusZero e
originalEightSlotRead centreOffset e Sites.sitePlusZero = plusZero e
originalEightSlotRead centreOffset e Sites.siteZeroMinus = zeroMinus e
originalEightSlotRead centreOffset e Sites.siteZeroPlus = zeroPlus e
originalEightSlotRead centreOffset e Sites.siteMinusMinus = minusMinus e
originalEightSlotRead centreOffset e Sites.sitePlusPlus = plusPlus e
originalEightSlotRead centreOffset e Sites.siteMinusPlus = minusPlus e
originalEightSlotRead centreOffset e Sites.sitePlusMinus = plusMinus e

module _
  {A : Set}
  (_⊕_ _⊖_ : A → A → A)
  (zero : A)
  (differenceCancel : ∀ a b → (a ⊖ b) ⊕ b ≡ a)
  (subtractAddedCentre : ∀ a b → (a ⊕ b) ⊖ b ≡ a)
  (selfDifferenceZero : ∀ a → a ⊖ a ≡ zero)
  where

  OriginalSheet : Set
  OriginalSheet = Torus.Torus3x3 → A

  originalCentre : OriginalSheet → A
  originalCentre f = f (Sites.sourceToOriginalTorus Sites.siteCentre)

  originalEightOffsets : OriginalSheet → OriginalPuncturedEight A
  originalEightOffsets f =
    puncturedEight
      (f (Sites.sourceToOriginalTorus Sites.siteMinusZero) ⊖ originalCentre f)
      (f (Sites.sourceToOriginalTorus Sites.sitePlusZero) ⊖ originalCentre f)
      (f (Sites.sourceToOriginalTorus Sites.siteZeroMinus) ⊖ originalCentre f)
      (f (Sites.sourceToOriginalTorus Sites.siteZeroPlus) ⊖ originalCentre f)
      (f (Sites.sourceToOriginalTorus Sites.siteMinusMinus) ⊖ originalCentre f)
      (f (Sites.sourceToOriginalTorus Sites.sitePlusPlus) ⊖ originalCentre f)
      (f (Sites.sourceToOriginalTorus Sites.siteMinusPlus) ⊖ originalCentre f)
      (f (Sites.sourceToOriginalTorus Sites.sitePlusMinus) ⊖ originalCentre f)

  reopenOriginalEightAt :
    A → OriginalPuncturedEight A → Sites.OriginalSourceSlot → A
  reopenOriginalEightAt c e Sites.siteCentre = c
  reopenOriginalEightAt c e Sites.siteMinusZero = minusZero e ⊕ c
  reopenOriginalEightAt c e Sites.sitePlusZero = plusZero e ⊕ c
  reopenOriginalEightAt c e Sites.siteZeroMinus = zeroMinus e ⊕ c
  reopenOriginalEightAt c e Sites.siteZeroPlus = zeroPlus e ⊕ c
  reopenOriginalEightAt c e Sites.siteMinusMinus = minusMinus e ⊕ c
  reopenOriginalEightAt c e Sites.sitePlusPlus = plusPlus e ⊕ c
  reopenOriginalEightAt c e Sites.siteMinusPlus = minusPlus e ⊕ c
  reopenOriginalEightAt c e Sites.sitePlusMinus = plusMinus e ⊕ c

  reopenOriginalEight :
    A → OriginalPuncturedEight A → OriginalSheet
  reopenOriginalEight c e point =
    reopenOriginalEightAt c e (Sites.originalTorusToSource point)

  -- Full source sheet reopens exactly from its original eight offsets
  -- and one independent centre, pointwise over ALL nine original slots.
  originalEightDecodeEncodeAt :
    (f : OriginalSheet) (slot : Sites.OriginalSourceSlot) →
    reopenOriginalEightAt (originalCentre f)
                          (originalEightOffsets f) slot
    ≡ f (Sites.sourceToOriginalTorus slot)
  originalEightDecodeEncodeAt f Sites.siteCentre = refl
  originalEightDecodeEncodeAt f Sites.siteMinusZero =
    differenceCancel (f (Sites.sourceToOriginalTorus Sites.siteMinusZero))
                     (originalCentre f)
  originalEightDecodeEncodeAt f Sites.sitePlusZero =
    differenceCancel (f (Sites.sourceToOriginalTorus Sites.sitePlusZero))
                     (originalCentre f)
  originalEightDecodeEncodeAt f Sites.siteZeroMinus =
    differenceCancel (f (Sites.sourceToOriginalTorus Sites.siteZeroMinus))
                     (originalCentre f)
  originalEightDecodeEncodeAt f Sites.siteZeroPlus =
    differenceCancel (f (Sites.sourceToOriginalTorus Sites.siteZeroPlus))
                     (originalCentre f)
  originalEightDecodeEncodeAt f Sites.siteMinusMinus =
    differenceCancel (f (Sites.sourceToOriginalTorus Sites.siteMinusMinus))
                     (originalCentre f)
  originalEightDecodeEncodeAt f Sites.sitePlusPlus =
    differenceCancel (f (Sites.sourceToOriginalTorus Sites.sitePlusPlus))
                     (originalCentre f)
  originalEightDecodeEncodeAt f Sites.siteMinusPlus =
    differenceCancel (f (Sites.sourceToOriginalTorus Sites.siteMinusPlus))
                     (originalCentre f)
  originalEightDecodeEncodeAt f Sites.sitePlusMinus =
    differenceCancel (f (Sites.sourceToOriginalTorus Sites.sitePlusMinus))
                     (originalCentre f)

  -- Conversely any eight + centre encoding returns exactly the
  -- original eight offsets when decoded/re-encoded. This includes
  -- the zero centre-relative slot separately.
  originalEightEncodeDecodeAt :
    (centre : A) (e : OriginalPuncturedEight A)
    (slot : Sites.OriginalSourceSlot) →
    (reopenOriginalEight centre e
       (Sites.sourceToOriginalTorus slot)
     ⊖ originalCentre (reopenOriginalEight centre e))
    ≡ originalEightSlotRead zero e slot
  originalEightEncodeDecodeAt centre e Sites.siteCentre =
    selfDifferenceZero centre
  originalEightEncodeDecodeAt centre e Sites.siteMinusZero =
    subtractAddedCentre (minusZero e) centre
  originalEightEncodeDecodeAt centre e Sites.sitePlusZero =
    subtractAddedCentre (plusZero e) centre
  originalEightEncodeDecodeAt centre e Sites.siteZeroMinus =
    subtractAddedCentre (zeroMinus e) centre
  originalEightEncodeDecodeAt centre e Sites.siteZeroPlus =
    subtractAddedCentre (zeroPlus e) centre
  originalEightEncodeDecodeAt centre e Sites.siteMinusMinus =
    subtractAddedCentre (minusMinus e) centre
  originalEightEncodeDecodeAt centre e Sites.sitePlusPlus =
    subtractAddedCentre (plusPlus e) centre
  originalEightEncodeDecodeAt centre e Sites.siteMinusPlus =
    subtractAddedCentre (minusPlus e) centre
  originalEightEncodeDecodeAt centre e Sites.sitePlusMinus =
    subtractAddedCentre (plusMinus e) centre

-- A05 still OPEN: instantiate over selected Z[omega]/real wave
-- coefficients and prove original Fourier-pair decode, exact
-- translation re-gauge, and original model source/consumer refinement.
