module DASHI.Algebra.SeparatedLeadingValuationExact where

------------------------------------------------------------------------
-- GENERIC NONARCHIMEDEAN LEADING-TERM CORE
--
-- If x has strictly smaller valuation than a remainder y, then x+y has exactly
-- the valuation of x.  This tiny abstraction is the reusable algebraic step
-- behind the p=5,7,11 Duncan--Swisher partial-fraction arguments.
--
-- No p-adic numbers or modular functions are built into the carrier.  A source
-- adapter must supply the actual addition law, valuation, and strict-minimum
-- theorem for its algebra.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import DASHI.Core.Prelude
open import Data.Nat using (_<_)

record StrictMinimumValuation {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    add : A → A → A
    valuation : A → Nat

    strictMinimumLaw :
      (x y : A) →
      valuation x < valuation y →
      valuation (add x y) ≡ valuation x

open StrictMinimumValuation public

record SeparatedLeadingTerm
    {ℓ : Level}
    {A : Set ℓ}
    (V : StrictMinimumValuation A)
    (total : A) : Set ℓ where
  field
    leading remainder : A
    decomposition : total ≡ add V leading remainder
    leadingStrictlyShallower :
      valuation V leading < valuation V remainder

open SeparatedLeadingTerm public

separatedLeadingDeterminesValuation :
  {ℓ : Level} →
  {A : Set ℓ} →
  (V : StrictMinimumValuation A) →
  (total : A) →
  (S : SeparatedLeadingTerm V total) →
  valuation V total ≡ valuation V (leading S)
separatedLeadingDeterminesValuation V total S =
  trans
    (cong (valuation V) (decomposition S))
    (strictMinimumLaw V
      (leading S)
      (remainder S)
      (leadingStrictlyShallower S))

record ExactLeadingDepth
    {ℓ : Level}
    {A : Set ℓ}
    (V : StrictMinimumValuation A)
    (total : A)
    (depth : Nat) : Set ℓ where
  field
    separation : SeparatedLeadingTerm V total
    leadingDepthExact : valuation V (leading separation) ≡ depth

open ExactLeadingDepth public

exactLeadingDepthDeterminesTotal :
  {ℓ : Level} →
  {A : Set ℓ} →
  (V : StrictMinimumValuation A) →
  (total : A) →
  (depth : Nat) →
  (E : ExactLeadingDepth V total depth) →
  valuation V total ≡ depth
exactLeadingDepthDeterminesTotal V total depth E =
  trans
    (separatedLeadingDeterminesValuation V total (separation E))
    (leadingDepthExact E)

record SeparatedLeadingValuationBoundary : Set where
  field
    carrierGeneric : Bool
    strictMinimumLawExplicit : Bool
    decompositionProofRelevant : Bool
    exactTotalDepthDerived : Bool
    padicSpecificStructureAssumed : Bool

canonicalSeparatedLeadingValuationBoundary :
  SeparatedLeadingValuationBoundary
canonicalSeparatedLeadingValuationBoundary = record
  { carrierGeneric = true
  ; strictMinimumLawExplicit = true
  ; decompositionProofRelevant = true
  ; exactTotalDepthDerived = true
  ; padicSpecificStructureAssumed = false
  }
