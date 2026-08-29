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
-- plus three distinguished phase directions living in one transverse sector.
-- The transverse carrier is labelled by three directions because a 120-degree
-- rotation has order three even though the ambient real transverse space is
-- two-dimensional.

data RelationalC3Mode : Set where
  fixedRelationalMode : RelationalC3Mode
  transversePhaseZero : RelationalC3Mode
  transversePhaseOne : RelationalC3Mode
  transversePhaseTwo : RelationalC3Mode

shiftMode : RelationalC3Mode → RelationalC3Mode
shiftMode fixedRelationalMode = fixedRelationalMode
shiftMode transversePhaseZero = transversePhaseOne
shiftMode transversePhaseOne = transversePhaseTwo
shiftMode transversePhaseTwo = transversePhaseZero

fixedModeIsFixed :
  shiftMode fixedRelationalMode ≡ fixedRelationalMode
fixedModeIsFixed = refl

transverseZeroNotFixed :
  shiftMode transversePhaseZero ≡ transversePhaseZero → ⊥
transverseZeroNotFixed ()

transverseOneNotFixed :
  shiftMode transversePhaseOne ≡ transversePhaseOne → ⊥
transverseOneNotFixed ()

transverseTwoNotFixed :
  shiftMode transversePhaseTwo ≡ transversePhaseTwo → ⊥
transverseTwoNotFixed ()

shiftModeCube :
  (m : RelationalC3Mode) →
  shiftMode (shiftMode (shiftMode m)) ≡ m
shiftModeCube fixedRelationalMode = refl
shiftModeCube transversePhaseZero = refl
shiftModeCube transversePhaseOne = refl
shiftModeCube transversePhaseTwo = refl

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

shiftStateCube :
  (s : FixedTransverseState) →
  shiftState (shiftState (shiftState s)) ≡ s
shiftStateCube (fixedTransverseState a fixedRelationalMode) = refl
shiftStateCube (fixedTransverseState a transversePhaseZero) = refl
shiftStateCube (fixedTransverseState a transversePhaseOne) = refl
shiftStateCube (fixedTransverseState a transversePhaseTwo) = refl

canonicalFixedState : FixedTransverseState
canonicalFixedState = fixedTransverseState 3 fixedRelationalMode

canonicalTransverseState : FixedTransverseState
canonicalTransverseState = fixedTransverseState 3 transversePhaseZero

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

    threePhaseDirectionsMeanTransverseDimensionThree : Bool
    threePhaseDirectionsMeanTransverseDimensionThreeIsFalse :
      threePhaseDirectionsMeanTransverseDimensionThree ≡ false

canonicalFixedTransverseBoundary : FixedTransverseBoundary
canonicalFixedTransverseBoundary =
  fixedTransverseBoundary false refl false refl false refl
