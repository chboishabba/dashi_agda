module DASHI.NumberTheory.Collatz.SyracuseAffineIterateCompilerExact where

------------------------------------------------------------------------
-- ONE-STEP -> ARBITRARY-ITERATE AFFINE COMPILER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine

record SyracuseOneStepAffineSource : Set₁ where
  field
    evenStepExact :
      (x : Syracuse.PositiveNat) →
      Itinerary.parity x ≡ false →
      2 * Syracuse.toNat (Syracuse.shortcutSyracuse x)
      ≡ Syracuse.toNat x

    oddStepExact :
      (x : Syracuse.PositiveNat) →
      Itinerary.parity x ≡ true →
      2 * Syracuse.toNat (Syracuse.shortcutSyracuse x)
      ≡ 3 * Syracuse.toNat x + 1

open SyracuseOneStepAffineSource public

scaleTwoProduct :
  (p z : Nat) →
  (2 * p) * z ≡ 2 * (p * z)
scaleTwoProduct =
  solve 2 (λ p z → ((con 2 :* p) :* z) := (con 2 :* (p :* z))) refl

evenAffineStep :
  (p next current a : Nat) →
  2 * next ≡ current →
  2 * (p * next + a) ≡ p * current + 2 * a
evenAffineStep p next current a step rewrite step =
  solve 3
    (λ p current a →
      (p :* current) :+ (con 2 :* a)
      :=
      (p :* current) :+ (con 2 :* a))
    refl

oddAffineStep :
  (p next current a : Nat) →
  2 * next ≡ 3 * current + 1 →
  2 * (p * next + a)
  ≡ (3 * p) * current + (p + 2 * a)
oddAffineStep p next current a step =
  let
    rearrange :
      2 * (p * next + a) ≡ p * (2 * next) + 2 * a
    rearrange =
      solve 3
        (λ p next a →
          con 2 :* ((p :* next) :+ a)
          :=
          (p :* (con 2 :* next)) :+ (con 2 :* a))
        refl

    afterStep :
      p * (2 * next) + 2 * a
      ≡ p * (3 * current + 1) + 2 * a
    afterStep = cong (λ value → p * value + 2 * a) step

    normalize :
      p * (3 * current + 1) + 2 * a
      ≡ (3 * p) * current + (p + 2 * a)
    normalize =
      solve 3
        (λ p current a →
          (p :* ((con 3 :* current) :+ con 1)) :+ (con 2 :* a)
          :=
          ((con 3 :* p) :* current) :+ (p :+ (con 2 :* a)))
        refl
  in
  trans rearrange (trans afterStep normalize)

compileAffineIterate :
  SyracuseOneStepAffineSource →
  (m : Nat) →
  (x : Syracuse.PositiveNat) →
  Affine.powNat 2 m
    * Syracuse.toNat (Syracuse.syracuseIterate m x)
  ≡
  Affine.powNat 3
      (Affine.parityCount (Itinerary.parityWord m x))
    * Syracuse.toNat x
  + Affine.affineAdditiveTerm (Itinerary.parityWord m x)
compileAffineIterate source zero x = refl
compileAffineIterate source (suc m) x with Itinerary.parity x
... | false =
  let
    next = Syracuse.shortcutSyracuse x
    p2 = Affine.powNat 2 m
    p3 = Affine.powNat 3
      (Affine.parityCount (Itinerary.parityWord m next))
    a = Affine.affineAdditiveTerm (Itinerary.parityWord m next)
    ih = compileAffineIterate source m next
    scaledIH = cong (λ value → 2 * value) ih
    leftAssoc = scaleTwoProduct p2
      (Syracuse.toNat (Syracuse.syracuseIterate m next))
    finish = evenAffineStep p3
      (Syracuse.toNat next)
      (Syracuse.toNat x)
      a
      (evenStepExact source x refl)
  in
  trans leftAssoc (trans scaledIH finish)
... | true =
  let
    next = Syracuse.shortcutSyracuse x
    p2 = Affine.powNat 2 m
    p3 = Affine.powNat 3
      (Affine.parityCount (Itinerary.parityWord m next))
    a = Affine.affineAdditiveTerm (Itinerary.parityWord m next)
    ih = compileAffineIterate source m next
    scaledIH = cong (λ value → 2 * value) ih
    leftAssoc = scaleTwoProduct p2
      (Syracuse.toNat (Syracuse.syracuseIterate m next))
    finish = oddAffineStep p3
      (Syracuse.toNat next)
      (Syracuse.toNat x)
      a
      (oddStepExact source x refl)
  in
  trans leftAssoc (trans scaledIH finish)

compileAffineIterateSource :
  SyracuseOneStepAffineSource →
  Affine.SyracuseAffineIterateSource
compileAffineIterateSource source = record
  { Affine.syracuseAffineIterateExact = compileAffineIterate source }

record AffineCompilerBoundary : Set where
  constructor affineCompilerBoundary
  field
    arbitraryIterateInductionOwned : Nat
    semiringRearrangementOwned : Nat
    onlyOneStepArithmeticRequired : Nat

canonicalAffineCompilerBoundary : AffineCompilerBoundary
canonicalAffineCompilerBoundary = affineCompilerBoundary 1 1 1
