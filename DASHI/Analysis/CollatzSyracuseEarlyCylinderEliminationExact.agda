module DASHI.Analysis.CollatzSyracuseEarlyCylinderEliminationExact where

------------------------------------------------------------------------
-- EARLY LITERAL SURVIVOR-CYLINDER ELIMINATION
--
-- The terminal tail has already been reduced to starts whose first two
-- literal Syracuse parity bits are 11.  Exact affine arithmetic pays three
-- additional cylinders uniformly on the existing x >= 8 tail:
--
--   1100  : 16 T^4(x) =  9 x +  5 < 16 x,
--   11010 : 32 T^5(x) = 27 x + 23 < 32 x,
--   11100 : 32 T^5(x) = 27 x + 19 < 32 x.
--
-- After splitting only on the actual orbit parity observer, every remaining
-- start lies in one of three literal residual prefix families:
--
--   11011, 11101, or 1111...
--
-- The compiler below does not assert that those residual families descend.
-- That residual producer remains the theorem-strength unbounded leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat using (_<_; _≤_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.NumberTheory.Collatz.SyracuseAffineDescentMarginExact as Margin
import DASHI.Analysis.CollatzSyracuseOddOddTailReductionExact as OddOdd
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Universal

step1 : Syracuse.PositiveNat → Syracuse.PositiveNat
step1 = Syracuse.shortcutSyracuse

step2 : Syracuse.PositiveNat → Syracuse.PositiveNat
step2 x = step1 (step1 x)

step3 : Syracuse.PositiveNat → Syracuse.PositiveNat
step3 x = step1 (step2 x)

step4 : Syracuse.PositiveNat → Syracuse.PositiveNat
step4 x = step1 (step3 x)

------------------------------------------------------------------------
-- Literal word identifications.
------------------------------------------------------------------------

word1100 :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ true →
  Itinerary.parity (step1 x) ≡ true →
  Itinerary.parity (step2 x) ≡ false →
  Itinerary.parity (step3 x) ≡ false →
  Itinerary.parityWord 4 x
  ≡ Binary.bit1 (Binary.bit1 (Binary.bit0 (Binary.bit0 Binary.end)))
word1100 x p0 p1 p2 p3
  rewrite p0 | p1 | p2 | p3 = refl

word11010 :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ true →
  Itinerary.parity (step1 x) ≡ true →
  Itinerary.parity (step2 x) ≡ false →
  Itinerary.parity (step3 x) ≡ true →
  Itinerary.parity (step4 x) ≡ false →
  Itinerary.parityWord 5 x
  ≡ Binary.bit1
      (Binary.bit1
        (Binary.bit0
          (Binary.bit1 (Binary.bit0 Binary.end))))
word11010 x p0 p1 p2 p3 p4
  rewrite p0 | p1 | p2 | p3 | p4 = refl

word11100 :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ true →
  Itinerary.parity (step1 x) ≡ true →
  Itinerary.parity (step2 x) ≡ true →
  Itinerary.parity (step3 x) ≡ false →
  Itinerary.parity (step4 x) ≡ false →
  Itinerary.parityWord 5 x
  ≡ Binary.bit1
      (Binary.bit1
        (Binary.bit1
          (Binary.bit0 (Binary.bit0 Binary.end))))
word11100 x p0 p1 p2 p3 p4
  rewrite p0 | p1 | p2 | p3 | p4 = refl

------------------------------------------------------------------------
-- Small tail inequalities.  These use only the already-existing x >= 8 cut.
------------------------------------------------------------------------

fiveBelowTail :
  (x : Nat) →
  8 ≤ x →
  5 < x
fiveBelowTail x lower =
  NatP.≤-trans
    (NatP.m≤m+n 6 2)
    lower

nineteenBelowThreeTail :
  (x : Nat) →
  8 ≤ x →
  19 < 3 * x
nineteenBelowThreeTail x lower =
  NatP.<-≤-trans
    (NatP.m≤m+n 20 4)
    (NatP.*-monoʳ-≤ 3 lower)

twentyThreeBelowThreeTail :
  (x : Nat) →
  8 ≤ x →
  23 < 3 * x
twentyThreeBelowThreeTail x lower =
  NatP.<-≤-trans
    NatP.≤-refl
    (NatP.*-monoʳ-≤ 3 lower)

ninePlusXNormalize :
  (x : Nat) →
  9 * x + x ≡ 10 * x
ninePlusXNormalize =
  solve 1
    (λ x → (con 9 :* x) :+ x := con 10 :* x)
    refl

thirtyNormalize :
  (x : Nat) →
  27 * x + 3 * x ≡ 30 * x
thirtyNormalize =
  solve 1
    (λ x → (con 27 :* x) :+ (con 3 :* x) := con 30 :* x)
    refl

------------------------------------------------------------------------
-- Exact affine margins and literal descent for the three killed leaves.
------------------------------------------------------------------------

prefix1100AffineMargin :
  (x : Syracuse.PositiveNat) →
  8 ≤ Syracuse.toNat x →
  Itinerary.parity x ≡ true →
  Itinerary.parity (step1 x) ≡ true →
  Itinerary.parity (step2 x) ≡ false →
  Itinerary.parity (step3 x) ≡ false →
  Margin.literalAffineNumerator 4 x
  < Affine.powNat 2 4 * Syracuse.toNat x
prefix1100AffineMargin x lower p0 p1 p2 p3
  rewrite word1100 x p0 p1 p2 p3 =
  let
    value = Syracuse.toNat x
    correctionBelow : 5 < value
    correctionBelow = fiveBelowTail value lower

    shifted : 9 * value + 5 < 9 * value + value
    shifted = NatP.+-monoˡ-< (9 * value) correctionBelow

    belowTen : 9 * value + 5 < 10 * value
    belowTen =
      subst
        (λ right → 9 * value + 5 < right)
        (ninePlusXNormalize value)
        shifted

    tenBelowSixteen : 10 * value ≤ 16 * value
    tenBelowSixteen =
      NatP.*-monoˡ-≤ value (NatP.m≤m+n 10 6)
  in
  NatP.<-≤-trans belowTen tenBelowSixteen

prefix1100StrictDescent :
  (x : Syracuse.PositiveNat) →
  8 ≤ Syracuse.toNat x →
  Itinerary.parity x ≡ true →
  Itinerary.parity (step1 x) ≡ true →
  Itinerary.parity (step2 x) ≡ false →
  Itinerary.parity (step3 x) ≡ false →
  Syracuse.toNat (Syracuse.syracuseIterate 4 x) < Syracuse.toNat x
prefix1100StrictDescent x lower p0 p1 p2 p3 =
  Margin.strictAffineMarginImpliesDescent
    4 x (prefix1100AffineMargin x lower p0 p1 p2 p3)

prefix11010AffineMargin :
  (x : Syracuse.PositiveNat) →
  8 ≤ Syracuse.toNat x →
  Itinerary.parity x ≡ true →
  Itinerary.parity (step1 x) ≡ true →
  Itinerary.parity (step2 x) ≡ false →
  Itinerary.parity (step3 x) ≡ true →
  Itinerary.parity (step4 x) ≡ false →
  Margin.literalAffineNumerator 5 x
  < Affine.powNat 2 5 * Syracuse.toNat x
prefix11010AffineMargin x lower p0 p1 p2 p3 p4
  rewrite word11010 x p0 p1 p2 p3 p4 =
  let
    value = Syracuse.toNat x
    correctionBelow : 23 < 3 * value
    correctionBelow = twentyThreeBelowThreeTail value lower

    shifted : 27 * value + 23 < 27 * value + 3 * value
    shifted = NatP.+-monoˡ-< (27 * value) correctionBelow

    belowThirty : 27 * value + 23 < 30 * value
    belowThirty =
      subst
        (λ right → 27 * value + 23 < right)
        (thirtyNormalize value)
        shifted

    thirtyBelowThirtyTwo : 30 * value ≤ 32 * value
    thirtyBelowThirtyTwo =
      NatP.*-monoˡ-≤ value (NatP.m≤m+n 30 2)
  in
  NatP.<-≤-trans belowThirty thirtyBelowThirtyTwo

prefix11010StrictDescent :
  (x : Syracuse.PositiveNat) →
  8 ≤ Syracuse.toNat x →
  Itinerary.parity x ≡ true →
  Itinerary.parity (step1 x) ≡ true →
  Itinerary.parity (step2 x) ≡ false →
  Itinerary.parity (step3 x) ≡ true →
  Itinerary.parity (step4 x) ≡ false →
  Syracuse.toNat (Syracuse.syracuseIterate 5 x) < Syracuse.toNat x
prefix11010StrictDescent x lower p0 p1 p2 p3 p4 =
  Margin.strictAffineMarginImpliesDescent
    5 x (prefix11010AffineMargin x lower p0 p1 p2 p3 p4)

prefix11100AffineMargin :
  (x : Syracuse.PositiveNat) →
  8 ≤ Syracuse.toNat x →
  Itinerary.parity x ≡ true →
  Itinerary.parity (step1 x) ≡ true →
  Itinerary.parity (step2 x) ≡ true →
  Itinerary.parity (step3 x) ≡ false →
  Itinerary.parity (step4 x) ≡ false →
  Margin.literalAffineNumerator 5 x
  < Affine.powNat 2 5 * Syracuse.toNat x
prefix11100AffineMargin x lower p0 p1 p2 p3 p4
  rewrite word11100 x p0 p1 p2 p3 p4 =
  let
    value = Syracuse.toNat x
    correctionBelow : 19 < 3 * value
    correctionBelow = nineteenBelowThreeTail value lower

    shifted : 27 * value + 19 < 27 * value + 3 * value
    shifted = NatP.+-monoˡ-< (27 * value) correctionBelow

    belowThirty : 27 * value + 19 < 30 * value
    belowThirty =
      subst
        (λ right → 27 * value + 19 < right)
        (thirtyNormalize value)
        shifted

    thirtyBelowThirtyTwo : 30 * value ≤ 32 * value
    thirtyBelowThirtyTwo =
      NatP.*-monoˡ-≤ value (NatP.m≤m+n 30 2)
  in
  NatP.<-≤-trans belowThirty thirtyBelowThirtyTwo

prefix11100StrictDescent :
  (x : Syracuse.PositiveNat) →
  8 ≤ Syracuse.toNat x →
  Itinerary.parity x ≡ true →
  Itinerary.parity (step1 x) ≡ true →
  Itinerary.parity (step2 x) ≡ true →
  Itinerary.parity (step3 x) ≡ false →
  Itinerary.parity (step4 x) ≡ false →
  Syracuse.toNat (Syracuse.syracuseIterate 5 x) < Syracuse.toNat x
prefix11100StrictDescent x lower p0 p1 p2 p3 p4 =
  Margin.strictAffineMarginImpliesDescent
    5 x (prefix11100AffineMargin x lower p0 p1 p2 p3 p4)

------------------------------------------------------------------------
-- Exact residual survivor families after those leaves are killed.
------------------------------------------------------------------------

data EarlyResidualPrefix (x : Syracuse.PositiveNat) : Set where
  residual11011 :
    Itinerary.parity x ≡ true →
    Itinerary.parity (step1 x) ≡ true →
    Itinerary.parity (step2 x) ≡ false →
    Itinerary.parity (step3 x) ≡ true →
    Itinerary.parity (step4 x) ≡ true →
    EarlyResidualPrefix x

  residual11101 :
    Itinerary.parity x ≡ true →
    Itinerary.parity (step1 x) ≡ true →
    Itinerary.parity (step2 x) ≡ true →
    Itinerary.parity (step3 x) ≡ false →
    Itinerary.parity (step4 x) ≡ true →
    EarlyResidualPrefix x

  residual1111 :
    Itinerary.parity x ≡ true →
    Itinerary.parity (step1 x) ≡ true →
    Itinerary.parity (step2 x) ≡ true →
    Itinerary.parity (step3 x) ≡ true →
    EarlyResidualPrefix x

record EarlyResidualTailSource : Set₁ where
  field
    residualDescend :
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      EarlyResidualPrefix x →
      Σ Nat (λ k →
        Syracuse.toNat (Syracuse.syracuseIterate k x)
        < Syracuse.toNat x)

open EarlyResidualTailSource public

asOddOddTailStrictDescentSource :
  EarlyResidualTailSource →
  OddOdd.OddOddTailStrictDescentAboveEightSource
asOddOddTailStrictDescentSource source = record
  { OddOdd.oddOddTailDescend = descend
  }
  where
    descend :
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      Itinerary.parity x ≡ true →
      Itinerary.parity (step1 x) ≡ true →
      Σ Nat (λ k →
        Syracuse.toNat (Syracuse.syracuseIterate k x)
        < Syracuse.toNat x)
    descend x lower nontrivial p0 p1
      with Itinerary.parity (step2 x) in p2
    ... | false with Itinerary.parity (step3 x) in p3
    ...   | false =
      4 , prefix1100StrictDescent x lower p0 p1 p2 p3
    ...   | true with Itinerary.parity (step4 x) in p4
    ...     | false =
      5 , prefix11010StrictDescent x lower p0 p1 p2 p3 p4
    ...     | true =
      residualDescend source x lower nontrivial
        (residual11011 p0 p1 p2 p3 p4)
    ... | true with Itinerary.parity (step3 x) in p3
    ...   | false with Itinerary.parity (step4 x) in p4
    ...     | false =
      5 , prefix11100StrictDescent x lower p0 p1 p2 p3 p4
    ...     | true =
      residualDescend source x lower nontrivial
        (residual11101 p0 p1 p2 p3 p4)
    ...   | true =
      residualDescend source x lower nontrivial
        (residual1111 p0 p1 p2 p3)

asLiteralStrictDescentSource :
  EarlyResidualTailSource →
  Universal.LiteralStrictDescentSource
asLiteralStrictDescentSource source =
  OddOdd.asLiteralStrictDescentSource
    (asOddOddTailStrictDescentSource source)

universalStoppingFromEarlyResidualTail :
  EarlyResidualTailSource →
  (x : Syracuse.PositiveNat) →
  Universal.ReachesOne x
universalStoppingFromEarlyResidualTail source =
  OddOdd.universalStoppingFromOddOddTail
    (asOddOddTailStrictDescentSource source)

record EarlyCylinderEliminationBoundary : Set where
  constructor earlyCylinderEliminationBoundary
  field
    prefix1100Paid : Nat
    prefix11010Paid : Nat
    prefix11100Paid : Nat
    residualThreeCylinderCompilerPaid : Nat
    densityPromotesResidual : Nat
    residualProducerPaid : Nat
    onlyUnboundedLeafIsResidualThreeCylinder : Nat

canonicalEarlyCylinderEliminationBoundary : EarlyCylinderEliminationBoundary
canonicalEarlyCylinderEliminationBoundary =
  earlyCylinderEliminationBoundary 1 1 1 1 0 0 1
