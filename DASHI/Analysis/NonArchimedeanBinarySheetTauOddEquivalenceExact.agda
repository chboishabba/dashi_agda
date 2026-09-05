module DASHI.Analysis.NonArchimedeanBinarySheetTauOddEquivalenceExact where

------------------------------------------------------------------------
-- EXACT BINARY-SHEET TAU-ODD EQUIVALENCE
--
-- This is the generic carrier theorem needed by the concrete Collatz sheet
-- decomposition.  It is independent of the spectral dynamics.
--
-- A half-function f : X -> S extends to X x {0,1} by
--
--   extend f (x,0) = f x
--   extend f (x,1) = - f x.
--
-- Restriction to sheet 0 recovers f definitionally.  Conversely, any full
-- function satisfying the tau-odd sheet law is recovered pointwise from its
-- sheet-0 restriction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)

record SheetPoint (Base : Set) : Set where
  constructor sheetPoint
  field
    base : Base
    sheet : Bool

open SheetPoint public

record NegationLaws (Scalar : Set) : Set₁ where
  field
    negate : Scalar → Scalar
    negateInvolutive : (x : Scalar) → negate (negate x) ≡ x

open NegationLaws public

HalfFunction : Set → Set → Set
HalfFunction Base Scalar = Base → Scalar

FullFunction : Set → Set → Set
FullFunction Base Scalar = SheetPoint Base → Scalar

antisymmetricExtend :
  ∀ {Base Scalar} →
  NegationLaws Scalar →
  HalfFunction Base Scalar →
  FullFunction Base Scalar
antisymmetricExtend laws f (sheetPoint x false) = f x
antisymmetricExtend laws f (sheetPoint x true) = negate laws (f x)

restrictSheetZero :
  ∀ {Base Scalar} →
  FullFunction Base Scalar →
  HalfFunction Base Scalar
restrictSheetZero F x = F (sheetPoint x false)

TauOddSheet :
  ∀ {Base Scalar} →
  NegationLaws Scalar →
  FullFunction Base Scalar → Set
TauOddSheet laws F =
  (x : Base) →
  F (sheetPoint x true) ≡ negate laws (F (sheetPoint x false))

extendIsTauOdd :
  ∀ {Base Scalar}
    (laws : NegationLaws Scalar)
    (f : HalfFunction Base Scalar) →
  TauOddSheet laws (antisymmetricExtend laws f)
extendIsTauOdd laws f x = refl

restrictAfterExtendPointwise :
  ∀ {Base Scalar}
    (laws : NegationLaws Scalar)
    (f : HalfFunction Base Scalar)
    (x : Base) →
  restrictSheetZero (antisymmetricExtend laws f) x ≡ f x
restrictAfterExtendPointwise laws f x = refl

extendAfterRestrictPointwise :
  ∀ {Base Scalar}
    (laws : NegationLaws Scalar)
    (F : FullFunction Base Scalar) →
  TauOddSheet laws F →
  (p : SheetPoint Base) →
  antisymmetricExtend laws (restrictSheetZero F) p ≡ F p
extendAfterRestrictPointwise laws F h (sheetPoint x false) = refl
extendAfterRestrictPointwise laws F h (sheetPoint x true) = sym (h x)

record BinarySheetWeldStatus : Set where
  constructor binarySheetWeldStatus
  field
    halfToTauOddExtensionOwned : Bool
    extensionIsTauOddOwned : Bool
    restrictionAfterExtensionOwned : Bool
    extensionAfterRestrictionPointwiseOwned : Bool
    genericCarrierEquivalenceStillOpen : Bool

canonicalBinarySheetWeldStatus : BinarySheetWeldStatus
canonicalBinarySheetWeldStatus =
  binarySheetWeldStatus true true true true false
