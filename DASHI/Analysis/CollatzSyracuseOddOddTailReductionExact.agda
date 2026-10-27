module DASHI.Analysis.CollatzSyracuseOddOddTailReductionExact where

------------------------------------------------------------------------
-- TERMINAL ODD-ODD TAIL REDUCTION
--
-- The previous max-cut pays every even start immediately.  Here we also pay
-- every odd start whose next literal Syracuse state is even.  Its two-step
-- parity word is 10 and the exact affine numerator is 3*x+1 over denominator
-- 4.  For x>1,
--
--   3*x + 1 < 3*x + x = 4*x,
--
-- so the existing exact affine-margin compiler gives literal strict descent.
-- The remaining unbounded source is therefore restricted to starts whose first
-- two literal parity bits are 11.  No residue heuristic or probability enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat using (_<_; _≤_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
import Data.Product as Product
open Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.NumberTheory.Collatz.SyracuseAffineDescentMarginExact as Margin
import DASHI.Analysis.CollatzSyracuseOddTailReductionExact as OddTail
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Universal

------------------------------------------------------------------------
-- Exact identification of the two-step odd/even parity word.
------------------------------------------------------------------------

oddEvenParityWord :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ true →
  Itinerary.parity (Syracuse.shortcutSyracuse x) ≡ false →
  Itinerary.parityWord 2 x
  ≡ Binary.bit1 (Binary.bit0 Binary.end)
oddEvenParityWord x odd nextEven
  rewrite odd | nextEven = refl

------------------------------------------------------------------------
-- Scalar margin for the 10 cylinder.
------------------------------------------------------------------------

threeXPlusOneLessFourX :
  (x : Nat) →
  1 < x →
  3 * x + 1 < 4 * x
threeXPlusOneLessFourX x nontrivial =
  let
    shifted : 3 * x + 1 < 3 * x + x
    shifted = NatP.+-monoˡ-< (3 * x) nontrivial

    normalize : 3 * x + x ≡ 4 * x
    normalize =
      solve 1
        (λ value →
          (con 3 :* value) :+ value
          := con 4 :* value)
        refl
  in
  subst (λ right → 3 * x + 1 < right) normalize shifted

oddEvenAffineMargin :
  (x : Syracuse.PositiveNat) →
  1 < Syracuse.toNat x →
  Itinerary.parity x ≡ true →
  Itinerary.parity (Syracuse.shortcutSyracuse x) ≡ false →
  Margin.literalAffineNumerator 2 x
  < Affine.powNat 2 2 * Syracuse.toNat x
oddEvenAffineMargin x nontrivial odd nextEven
  rewrite oddEvenParityWord x odd nextEven =
  threeXPlusOneLessFourX (Syracuse.toNat x) nontrivial

oddEvenTwoStepStrictDescent :
  (x : Syracuse.PositiveNat) →
  1 < Syracuse.toNat x →
  Itinerary.parity x ≡ true →
  Itinerary.parity (Syracuse.shortcutSyracuse x) ≡ false →
  Syracuse.toNat (Syracuse.syracuseIterate 2 x)
  < Syracuse.toNat x
oddEvenTwoStepStrictDescent x nontrivial odd nextEven =
  Margin.strictAffineMarginImpliesDescent
    2 x (oddEvenAffineMargin x nontrivial odd nextEven)

------------------------------------------------------------------------
-- Only literal 11-prefix starts remain source-specific.
------------------------------------------------------------------------

record OddOddTailStrictDescentAboveEightSource : Set₁ where
  field
    oddOddTailDescend :
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      Itinerary.parity x ≡ true →
      Itinerary.parity (Syracuse.shortcutSyracuse x) ≡ true →
      Σ Nat (λ k →
        Syracuse.toNat (Syracuse.syracuseIterate k x)
        < Syracuse.toNat x)

open OddOddTailStrictDescentAboveEightSource public

asOddTailStrictDescentSource :
  OddOddTailStrictDescentAboveEightSource →
  OddTail.OddTailStrictDescentAboveEightSource
asOddTailStrictDescentSource source = record
  { OddTail.oddTailDescend = tail
  }
  where
    tail :
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      Itinerary.parity x ≡ true →
      Σ Nat (λ k →
        Syracuse.toNat (Syracuse.syracuseIterate k x)
        < Syracuse.toNat x)
    tail x lower nontrivial odd
      with Itinerary.parity (Syracuse.shortcutSyracuse x) in secondParity
    ... | false =
      2 , oddEvenTwoStepStrictDescent x nontrivial odd secondParity
    ... | true =
      oddOddTailDescend source x lower nontrivial odd secondParity

asLiteralStrictDescentSource :
  OddOddTailStrictDescentAboveEightSource →
  Universal.LiteralStrictDescentSource
asLiteralStrictDescentSource source =
  OddTail.asLiteralStrictDescentSource
    (asOddTailStrictDescentSource source)

universalStoppingFromOddOddTail :
  OddOddTailStrictDescentAboveEightSource →
  (x : Syracuse.PositiveNat) →
  Universal.ReachesOne x
universalStoppingFromOddOddTail source =
  OddTail.universalStoppingFromOddTail
    (asOddTailStrictDescentSource source)

record OddOddTailReductionBoundary : Set where
  constructor oddOddTailReductionBoundary
  field
    evenStartsAlreadyPaid : Nat
    oddEvenWordExact : Nat
    oddEvenAffineMarginPaid : Nat
    oddEvenTwoStepDescentPaid : Nat
    oddOddTailCompilerPaid : Nat
    densityPromotesOddOddTail : Nat
    oddOddTailProducerPaid : Nat
    onlyUnboundedLeafIsOddOddTail : Nat

canonicalOddOddTailReductionBoundary : OddOddTailReductionBoundary
canonicalOddOddTailReductionBoundary =
  oddOddTailReductionBoundary 1 1 1 1 1 0 0 1
