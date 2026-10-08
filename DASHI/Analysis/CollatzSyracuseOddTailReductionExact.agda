module DASHI.Analysis.CollatzSyracuseOddTailReductionExact where

------------------------------------------------------------------------
-- TERMINAL ODD-TAIL REDUCTION
--
-- The literal shortcut Syracuse map pays every even nontrivial start in one
-- step.  Therefore the genuine unbounded terminal source only needs to cover
-- odd starts.  This is a same-object reduction on the literal integer map; no
-- density, finite sampling, or spectral argument is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat using (_<_; _≤_; s≤s; z≤n)
open import Data.Nat.Base using (NonZero; nonZero)
open import Data.Nat.DivMod using (m/n<m)
import Data.Product as Product
open Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseOneStepArithmeticExact as OneStep
import DASHI.Analysis.CollatzSyracuseStrictDescentBaseTailExact as BaseTail
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Universal

------------------------------------------------------------------------
-- Exact even branch = division by two, then strict descent because 2 >= 2.
------------------------------------------------------------------------

evenStepToNatQuotient :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ false →
  Syracuse.toNat (Syracuse.shortcutSyracuse x)
  ≡ Syracuse.toNat x / 2
evenStepToNatQuotient x@(Syracuse.positiveNat n) parityFalse =
  trans
    (cong Syracuse.toNat
      (Syracuse.shortcutSyracuseParityFalse n parityFalse))
    (OneStep.sucPredPositiveQuotient x parityFalse)

evenStartStrictDescent :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ false →
  Σ Nat (λ k →
    Syracuse.toNat (Syracuse.syracuseIterate k x)
    < Syracuse.toNat x)
evenStartStrictDescent x@(Syracuse.positiveNat n) parityFalse =
  let
    instance
      xNonZero : NonZero (Syracuse.toNat x)
      xNonZero = nonZero

    quotientSmaller : Syracuse.toNat x / 2 < Syracuse.toNat x
    quotientSmaller = m/n<m (Syracuse.toNat x) 2 (s≤s (s≤s z≤n))

    stepSmaller :
      Syracuse.toNat (Syracuse.shortcutSyracuse x) < Syracuse.toNat x
    stepSmaller =
      subst
        (λ value → value < Syracuse.toNat x)
        (sym (evenStepToNatQuotient x parityFalse))
        quotientSmaller
  in
  1 , stepSmaller

------------------------------------------------------------------------
-- Only odd starts above the already-paid finite base remain source-specific.
------------------------------------------------------------------------

record OddTailStrictDescentAboveEightSource : Set₁ where
  field
    oddTailDescend :
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      Itinerary.parity x ≡ true →
      Σ Nat (λ k →
        Syracuse.toNat (Syracuse.syracuseIterate k x)
        < Syracuse.toNat x)

open OddTailStrictDescentAboveEightSource public

asTailStrictDescentAboveEightSource :
  OddTailStrictDescentAboveEightSource →
  BaseTail.TailStrictDescentAboveEightSource
asTailStrictDescentAboveEightSource source = record
  { BaseTail.tailDescend = tail
  }
  where
    tail :
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      Σ Nat (λ k →
        Syracuse.toNat (Syracuse.syracuseIterate k x)
        < Syracuse.toNat x)
    tail x lower nontrivial with Itinerary.parity x in parityEq
    ... | false = evenStartStrictDescent x parityEq
    ... | true = oddTailDescend source x lower nontrivial parityEq

asLiteralStrictDescentSource :
  OddTailStrictDescentAboveEightSource →
  Universal.LiteralStrictDescentSource
asLiteralStrictDescentSource source =
  BaseTail.strictDescentFromBaseAndTail
    (asTailStrictDescentAboveEightSource source)

universalStoppingFromOddTail :
  OddTailStrictDescentAboveEightSource →
  (x : Syracuse.PositiveNat) →
  Universal.ReachesOne x
universalStoppingFromOddTail source =
  BaseTail.universalStoppingFromBaseAndTail
    (asTailStrictDescentAboveEightSource source)

record OddTailReductionBoundary : Set where
  constructor oddTailReductionBoundary
  field
    evenBranchExactQuotientPaid : Nat
    evenStartsStrictDescentPaid : Nat
    oddTailCompilerPaid : Nat
    finiteBaseStillPaidSeparately : Nat
    densityPromotesOddTail : Nat
    oddTailProducerPaid : Nat
    onlyUnboundedLeafIsOddTail : Nat

canonicalOddTailReductionBoundary : OddTailReductionBoundary
canonicalOddTailReductionBoundary =
  oddTailReductionBoundary 1 1 1 1 0 0 1
