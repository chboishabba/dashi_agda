module DASHI.ComputerScience.TekumFormalPropertiesExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem

------------------------------------------------------------------------
-- Kernel-owned consequences and explicit interfaces for Hunhold Props 2--5.

negationKeepsAnchor :
  ∀ {n} (x : Anchor.AnchoredTekum n) →
  Anchor.anchorFieldsCertified (Anchor.negateAnchored x)
  ≡ Anchor.anchorFieldsCertified x
negationKeepsAnchor (Anchor.anchoredTekum s a) = refl

record TekumInjectivityWitness (Word : Set) : Set₁ where
  field
    decode : Word → Sem.TekumValue
    decodeInjective :
      (x y : Word) → decode x ≡ decode y → x ≡ y

record TekumOrderedCodeWitness (Word : Set) : Set₁ where
  field
    codeLess : Word → Word → Set
    valueLess : Sem.TekumValue → Sem.TekumValue → Set
    decode : Word → Sem.TekumValue
    monotone :
      (x y : Word) → codeLess x y → valueLess (decode x) (decode y)

record TekumTruncationRoundingWitness
  (High Low : Set) : Set₁ where
  field
    truncateAnchor : High → Low
    nearest : High → Low → Set
    truncationIsNearest :
      (x : High) → nearest x (truncateAnchor x)

record TekumPrecisionComposition
  (High Mid Low : Set) : Set₁ where
  field
    highToMid : High → Mid
    midToLow : Mid → Low
    highToLow : High → Low
    compositional :
      (x : High) → midToLow (highToMid x) ≡ highToLow x

record TekumFormalPropertyBoundary : Set where
  constructor tekumFormalPropertyBoundary
  field
    proposition2InjectivityHasTypedTarget : Bool
    proposition3NegationAnchorInvariancePaid : Bool
    proposition4MonotonicityHasTypedTarget : Bool
    proposition5TruncationNearestHasTypedTarget : Bool
    doubleRoundingCompositionHasTypedTarget : Bool

canonicalTekumFormalPropertyBoundary : TekumFormalPropertyBoundary
canonicalTekumFormalPropertyBoundary =
  tekumFormalPropertyBoundary true true true true true
