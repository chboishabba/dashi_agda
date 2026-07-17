module DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds where

------------------------------------------------------------------------
-- Literal finite-lattice bond carrier for the Bałaban operator lane.
--
-- Vertices are the existing periodic four-coordinate carrier `Cube4 N`.
-- A directed bond is a source vertex, one of the four coordinate axes, and
-- an orientation.  Its target and reversal are computed from the already
-- proved periodic forward/backward shifts.
--
-- This is concrete finite geometry.  It introduces no gauge-group carrier,
-- source theorem import, analytic estimate, or Clay-status surface.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4
  ; Axis4
  ; FaceOrientation
  ; forward
  ; backward
  ; shiftForward
  ; shiftBackward
  ; shiftForwardBackward
  ; shiftBackwardForward
  )

record DirectedBond4 (N : Nat) : Set where
  constructor bond4
  field
    source      : Cube4 N
    axis        : Axis4
    orientation : FaceOrientation

open DirectedBond4 public

target :
  ∀ {N : Nat} → {{_ : NonZero N}} →
  DirectedBond4 N → Cube4 N
target (bond4 x a forward) = shiftForward a x
target (bond4 x a backward) = shiftBackward a x

positiveBond :
  ∀ {N : Nat} →
  Cube4 N → Axis4 → DirectedBond4 N
positiveBond x a = bond4 x a forward

negativeBond :
  ∀ {N : Nat} → {{_ : NonZero N}} →
  Cube4 N → Axis4 → DirectedBond4 N
negativeBond x a = bond4 (shiftForward a x) a backward

reverseBond :
  ∀ {N : Nat} → {{_ : NonZero N}} →
  DirectedBond4 N → DirectedBond4 N
reverseBond (bond4 x a forward) =
  bond4 (shiftForward a x) a backward
reverseBond (bond4 x a backward) =
  bond4 (shiftBackward a x) a forward

reverseSourceIsTarget :
  ∀ {N : Nat} {{_ : NonZero N}} (b : DirectedBond4 N) →
  source (reverseBond b) ≡ target b
reverseSourceIsTarget (bond4 x a forward) = refl
reverseSourceIsTarget (bond4 x a backward) = refl

reverseTargetIsSource :
  ∀ {N : Nat} {{_ : NonZero N}} (b : DirectedBond4 N) →
  target (reverseBond b) ≡ source b
reverseTargetIsSource (bond4 x a forward) =
  shiftBackwardForward a x
reverseTargetIsSource (bond4 x a backward) =
  shiftForwardBackward a x

reverseBondInvolutive :
  ∀ {N : Nat} {{_ : NonZero N}} (b : DirectedBond4 N) →
  reverseBond (reverseBond b) ≡ b
reverseBondInvolutive (bond4 x a forward) =
  cong (λ y → bond4 y a forward) (shiftBackwardForward a x)
reverseBondInvolutive (bond4 x a backward) =
  cong (λ y → bond4 y a backward) (shiftForwardBackward a x)

negativeBondIsReversePositive :
  ∀ {N : Nat} {{_ : NonZero N}}
  (x : Cube4 N) (a : Axis4) →
  negativeBond x a ≡ reverseBond (positiveBond x a)
negativeBondIsReversePositive x a = refl

positiveBondTarget :
  ∀ {N : Nat} {{_ : NonZero N}}
  (x : Cube4 N) (a : Axis4) →
  target (positiveBond x a) ≡ shiftForward a x
positiveBondTarget x a = refl

negativeBondTarget :
  ∀ {N : Nat} {{_ : NonZero N}}
  (x : Cube4 N) (a : Axis4) →
  target (negativeBond x a) ≡ x
negativeBondTarget x a = shiftBackwardForward a x
