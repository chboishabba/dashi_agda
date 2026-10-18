module DASHI.ComputerScience.TekumWidthAdmissibilityExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

record EvenWidth (n : Nat) : Set where
  constructor evenWidth
  field
    half : Nat
    twiceHalf : 2 * half ≡ n
open EvenWidth public

width8Even : EvenWidth 8
width8Even = evenWidth 4 refl

width10Even : EvenWidth 10
width10Even = evenWidth 5 refl

width20Even : EvenWidth 20
width20Even = evenWidth 10 refl

width40Even : EvenWidth 40
width40Even = evenWidth 20 refl

record CoreTekumWidth (n : Nat) : Set where
  constructor coreTekumWidth
  field
    even : EvenWidth n
    atLeastEightEvidence : Bool
open CoreTekumWidth public

canonicalWidth8 : CoreTekumWidth 8
canonicalWidth8 = coreTekumWidth width8Even true

record TekumWidthBoundary : Set where
  constructor tekumWidthBoundary
  field
    coreFormatUsesEvenWidths : Bool
    coreDefinitionStartsAtEightTrits : Bool
    sourceAlsoDefinesSmallerWidthsBySpecialCaseExtension : Bool

canonicalTekumWidthBoundary : TekumWidthBoundary
canonicalTekumWidthBoundary =
  tekumWidthBoundary true true true
