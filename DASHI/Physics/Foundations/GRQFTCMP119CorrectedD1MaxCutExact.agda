{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119CorrectedD1MaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeD1ReductionRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP116SharedFirstVariationCoordinateRound256Exact as R256

------------------------------------------------------------------------
-- CORRECTED D1 MAX-CUT
--
-- Historical Round228 split:
--
--   D1a  BC2.firstVariation has ordinary physical derivative semantics.
--   D1b  toPhysicalTangent = firstSubstitutionVariation.
--
-- Round256 proves that old D1b wording is type-wrong: the two maps land in
-- BackgroundTangent and LocalTangent respectively.  The local substitution
-- direction is their sequential composition and is already compiler plumbing.
--
-- Therefore the live physical seam is:
--
--   * D1a: the BC2 first-variation congruence/zero/add laws on the exact
--          present-cut carrier;
--   * D1b': the actual first-order derivative semantics of the physical
--           composite background transport, represented by Round152's
--           PhysicalCompositeD1ChainRule.
--
-- Once those are supplied, localized component D1 and the finite sum are
-- compiler-owned.
------------------------------------------------------------------------

record CorrectedCMP119D1PhysicalSemantics
    {History Cell : Set} {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs History Cell cutoff)
    : Set₁ where
  field
    d1aBC2FirstVariationLinearity :
      R143.PresentCutBC2FirstVariationLinearity present

    d1bPhysicalBackgroundTransportDerivative :
      R152.PhysicalCompositeD1ChainRule
        present d1aBC2FirstVariationLinearity

open CorrectedCMP119D1PhysicalSemantics public

oldD1bTangentFibreEqualityRequired : Bool
oldD1bTangentFibreEqualityRequired = false

oldD1bTangentFibreEqualityRequiredIsFalse :
  oldD1bTangentFibreEqualityRequired ≡ false
oldD1bTangentFibreEqualityRequiredIsFalse = refl

round256SequentialTangentCompositionCompilerOwned : Bool
round256SequentialTangentCompositionCompilerOwned = true

round256SequentialTangentCompositionCompilerOwnedIsTrue :
  round256SequentialTangentCompositionCompilerOwned ≡ true
round256SequentialTangentCompositionCompilerOwnedIsTrue = refl

d1aStillTheoremBearing : Bool
d1aStillTheoremBearing = true

d1aStillTheoremBearingIsTrue :
  d1aStillTheoremBearing ≡ true
d1aStillTheoremBearingIsTrue = refl

correctedD1bStillTheoremBearing : Bool
correctedD1bStillTheoremBearing = true

correctedD1bStillTheoremBearingIsTrue :
  correctedD1bStillTheoremBearing ≡ true
correctedD1bStillTheoremBearingIsTrue = refl
