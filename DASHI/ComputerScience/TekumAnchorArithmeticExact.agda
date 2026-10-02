module DASHI.ComputerScience.TekumAnchorArithmeticExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)

------------------------------------------------------------------------
-- Hunhold Definition 7:
--   anc_n(t) = |t| - 11...1.
--
-- This owner states the exact algebra needed from any fixed-width balanced
-- arithmetic backend and proves the load-bearing negation invariance once
-- abs(-t)=abs(t) is supplied.

record FixedWidthBalancedArithmetic (n : Nat) : Set₁ where
  field
    Word : Set
    negate : Word → Word
    modulus : Word → Word
    subtract : Word → Word → Word
    allOnes : Word
    modulusNegate :
      (x : Word) → modulus (negate x) ≡ modulus x
open FixedWidthBalancedArithmetic public

anchor :
  ∀ {n} (A : FixedWidthBalancedArithmetic n) →
  Word A → Word A
anchor A x = subtract A (modulus A x) (allOnes A)

anchorNegationInvariant :
  ∀ {n} (A : FixedWidthBalancedArithmetic n) (x : Word A) →
  anchor A (negate A x) ≡ anchor A x
anchorNegationInvariant A x =
  cong (λ y → subtract A y (allOnes A)) (modulusNegate A x)

record TekumAnchorArithmeticBoundary : Set where
  constructor tekumAnchorArithmeticBoundary
  field
    sourceDefinitionRepresentedLiterally : Bool
    negationInvarianceIsCompilerOwned : Bool
    fixedWidthAdderBackendRemainsSelectable : Bool

canonicalTekumAnchorArithmeticBoundary : TekumAnchorArithmeticBoundary
canonicalTekumAnchorArithmeticBoundary =
  tekumAnchorArithmeticBoundary true true true
