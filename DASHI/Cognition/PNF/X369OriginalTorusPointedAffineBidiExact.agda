module DASHI.Cognition.PNF.X369OriginalTorusPointedAffineBidiExact where

-- X369 A05: pointwise centre-plus-offset and induced translation law on
-- the ORIGINAL FiniteThreeCycleTorusExact.Torus3x3 carrier.  No duplicate
-- nine-point group and no manufactured learned/physical identification.
--
-- The algebra is explicitly PARAMETERISED by a cancellative affine
-- difference law.  This is a conditional theorem, not a postulate or
-- an unconditional claim about all coefficient rings / PyTorch floats.
-- Remaining: instantiate the selected exact Fourier coefficient ring,
-- prove Fourier/inverse transport and bridge to the original Leech chart.
--
-- The corresponding independent exact integer coefficient reference is
-- LeechTransformer PR #4:
-- scripts/certify_x369_original_torus_maxcut.py.

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus
import DASHI.Cognition.PNF.X369OriginalTorusGroupLawExact as Group

module _
  {A : Set}
  (_⊕_ _⊖_ : A → A → A)
  (zero : A)
  (differenceCancel : ∀ a b → (a ⊖ b) ⊕ b ≡ a)
  (selfDifferenceZero : ∀ a → a ⊖ a ≡ zero)
  (differenceGaugeCancel :
    ∀ a b c → (a ⊖ c) ⊖ (b ⊖ c) ≡ a ⊖ b)
  where

  OriginalSheet : Set
  OriginalSheet = Torus.Torus3x3 → A

  originalCentre : OriginalSheet → A
  originalCentre f = f Group.originalTorusZero

  originalOffsets : OriginalSheet → OriginalSheet
  originalOffsets f point = f point ⊖ originalCentre f

  reopenOriginalSheet : A → OriginalSheet → OriginalSheet
  reopenOriginalSheet centre offsets point =
    offsets point ⊕ centre

  -- The centre is an independent side state.  Reopening is
  -- pointwise exact at EVERY ORIGINAL torus point (including origin).
  originalPointedReopenBidi :
    (f : OriginalSheet) (point : Torus.Torus3x3) →
    reopenOriginalSheet (originalCentre f) (originalOffsets f) point
    ≡ f point
  originalPointedReopenBidi f point =
    differenceCancel (f point) (originalCentre f)

  -- The distinguished origin offset is zero; the other eight
  -- offsets plus the retained centre determine the full sheet.
  originalOffsetsCentreIsZero :
    (f : OriginalSheet) →
    originalOffsets f Group.originalTorusZero ≡ zero
  originalOffsetsCentreIsZero f =
    selfDifferenceZero (originalCentre f)

  translateOriginalSheet :
    OriginalSheet → Torus.Torus3x3 → OriginalSheet
  translateOriginalSheet f shift point =
    f (Group.originalTorusAdd
         point (Group.originalTorusInverse shift))

  -- Correct induced action is translation FOLLOWED BY RE-GAUGING
  -- against the translated origin; it is not a naive permutation
  -- of the eight centre-relative amplitudes.
  translatePointedOffsets :
    OriginalSheet → Torus.Torus3x3 → OriginalSheet
  translatePointedOffsets offsets shift point =
    offsets (Group.originalTorusAdd
              point (Group.originalTorusInverse shift))
    ⊖ offsets (Group.originalTorusAdd
                Group.originalTorusZero
                (Group.originalTorusInverse shift))

  originalPointedTranslationGaugeLaw :
    (f : OriginalSheet) (shift point : Torus.Torus3x3) →
    translatePointedOffsets (originalOffsets f) shift point
    ≡ originalOffsets (translateOriginalSheet f shift) point
  originalPointedTranslationGaugeLaw f shift point =
    differenceGaugeCancel
      (f (Group.originalTorusAdd
            point (Group.originalTorusInverse shift)))
      (f (Group.originalTorusAdd
            Group.originalTorusZero
            (Group.originalTorusInverse shift)))
      (originalCentre f)

-- Still OPEN: A03 finite Fourier inverse/convolution and A04 spectral
-- Parseval/conjugation in Agda, plus A05 Fourier-pair map, full original
-- source binding, signed floating-point refinement and Agda kernel run.
