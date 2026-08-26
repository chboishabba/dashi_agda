module DASHI.Biology.TernaryFixedTransverseFiniteExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite repo-native shadow of Aristotle's real C3 representation theorem.
--
-- Source theorem owner in the supplied archive:
--   Lean/Spine/TernaryPhase.lean
--
-- There the real regular C3 carrier splits as a one-dimensional fixed sector
-- plus a two-dimensional mean-zero transverse sector, and the cyclic shift has
-- no nonzero real eigenline in the transverse sector.  We do not manufacture
-- real linear algebra here.  Instead we expose the exact finite decomposition
-- needed by downstream visual/neural consumers: a common amplitude coordinate
-- plus a relational phase coordinate whose non-fixed part cycles.

data RelationalC3Mode : Set where
  fixedRelationalMode : RelationalC3Mode
  transverseModeA : RelationalC3Mode
  transverseModeB : RelationalC3Mode

shiftMode : RelationalC3Mode → RelationalC3Mode
shiftMode fixedRelationalMode = fixedRelationalMode
shiftMode transverseModeA = transverseModeB
shiftMode transverseModeB = transverseModeA

fixedModeIsFixed :
  shiftMode fixedRelationalMode ≡ fixedRelationalMode
fixedModeIsFixed = refl

transverseANotFixed :
  shiftMode transverseModeA ≡ transverseModeA → ⊥
transverseANotFixed ()

transverseBNotFixed :
  shiftMode transverseModeB ≡ transverseModeB → ⊥
transverseBNotFixed ()

shiftModeInvolutiveOnFiniteShadow :
  (m : RelationalC3Mode) → shiftMode (shiftMode m) ≡ m
shiftModeInvolutiveOnFiniteShadow fixedRelationalMode = refl
shiftModeInvolutiveOnFiniteShadow transverseModeA = refl
shiftModeInvolutiveOnFiniteShadow transverseModeB = refl

------------------------------------------------------------------------
-- Common activation is carried independently from relational mode.

record FixedTransverseState : Set where
  constructor fixedTransverseState
  field
    commonAmplitude : Nat
    relationalMode : RelationalC3Mode

open FixedTransverseState public

shiftState : FixedTransverseState → FixedTransverseState
shiftState (fixedTransverseState a m) =
  fixedTransverseState a (shiftMode m)

shiftPreservesCommonAmplitude :
  (s : FixedTransverseState) →
  commonAmplitude (shiftState s) ≡ commonAmplitude s
shiftPreservesCommonAmplitude (fixedTransverseState a m) = refl

canonicalFixedState : FixedTransverseState
canonicalFixedState = fixedTransverseState 3 fixedRelationalMode

canonicalTransverseState : FixedTransverseState
canonicalTransverseState = fixedTransverseState 3 transverseModeA

sameCommonAmplitudeDifferentRelationalMode :
  commonAmplitude canonicalFixedState
  ≡ commonAmplitude canonicalTransverseState
sameCommonAmplitudeDifferentRelationalMode = refl

relationalModesRemainDistinct :
  relationalMode canonicalFixedState
  ≡ relationalMode canonicalTransverseState
  → ⊥
relationalModesRemainDistinct ()

record FixedTransverseBoundary : Set where
  constructor fixedTransverseBoundary
  field
    finiteShadowIsFullRealRepresentationTheorem : Bool
    finiteShadowIsFullRealRepresentationTheoremIsFalse :
      finiteShadowIsFullRealRepresentationTheorem ≡ false

    commonAmplitudeDeterminesRelationalMode : Bool
    commonAmplitudeDeterminesRelationalModeIsFalse :
      commonAmplitudeDeterminesRelationalMode ≡ false

canonicalFixedTransverseBoundary : FixedTransverseBoundary
canonicalFixedTransverseBoundary =
  fixedTransverseBoundary false refl false refl
