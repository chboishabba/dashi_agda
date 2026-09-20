module DASHI.Physics.Closure.NSTriadKNR540OffDiagonalToLiteralR571M2Exact where

------------------------------------------------------------------------
-- PERIODIC B / R540 ORDERED OFF-DIAGONAL -> R571 SECOND MOMENT
--
-- The earlier R567 full-square M2 interface is stronger than the physical
-- problem requires and is incompatible with the intended displacement meaning
-- on diagonal cells: alpha = beta forces displacement zero, while the literal
-- forcing diagonal need not vanish.
--
-- The actual R406 residual is already represented exactly by R540 on the
-- ORDERED OFF-DIAGONAL carrier.  This owner puts the R571 second-moment
-- compiler on that carrier instead.
--
-- No cardinality factor, diagonal completion, positivity of the signed pair
-- scalar, or absolute-value sum is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment
import DASHI.Physics.Closure.NSTriadKNR571PreferredOneSidedSecondMomentExact as Preferred

------------------------------------------------------------------------
-- 1. Same-object pointwise producer for one ordered off-diagonal cell.
------------------------------------------------------------------------

record OrderedOffDiagonalR571Correspondence (A : Set) : Set₁ where
  field
    pairScalar : A → A → ℚ

    pairToSample :
      (left right : A) →
      Moment.PairedSecondMomentSample

    preferredBudget :
      Moment.PairedSecondMomentBudget

    pairBelowPairedMagnitude :
      (left right : A) →
      pairScalar left right
      ≤ Moment.pairedMagnitude (pairToSample left right)

    preferredPointwise :
      (left right : A) →
      Moment.pairedMagnitude (pairToSample left right)
      ≤ Moment.weightedSecondMoment (pairToSample left right)
        * Preferred.preferredCoefficient preferredBudget

open OrderedOffDiagonalR571Correspondence public

pairBelowPreferredM2 :
  ∀ {A} →
  (C : OrderedOffDiagonalR571Correspondence A) →
  (left right : A) →
  pairScalar C left right
  ≤ Moment.weightedSecondMoment (pairToSample C left right)
    * Preferred.preferredCoefficient (preferredBudget C)
pairBelowPreferredM2 C left right =
  ℚP.≤-trans
    (pairBelowPairedMagnitude C left right)
    (preferredPointwise C left right)

------------------------------------------------------------------------
-- 2. Literal ordered off-diagonal M2 fold with exactly R539's recursion.
------------------------------------------------------------------------

rowM2 :
  ∀ {A} →
  (C : OrderedOffDiagonalR571Correspondence A) →
  A → List A → ℚ
rowM2 C left [] = 0ℚ
rowM2 C left (right ∷ rest) =
  Moment.weightedSecondMoment (pairToSample C left right)
    * Preferred.preferredCoefficient (preferredBudget C)
  + rowM2 C left rest

columnM2 :
  ∀ {A} →
  (C : OrderedOffDiagonalR571Correspondence A) →
  List A → A → ℚ
columnM2 C [] right = 0ℚ
columnM2 C (left ∷ rest) right =
  Moment.weightedSecondMoment (pairToSample C left right)
    * Preferred.preferredCoefficient (preferredBudget C)
  + columnM2 C rest right

orderedOffDiagonalM2 :
  ∀ {A} →
  (C : OrderedOffDiagonalR571Correspondence A) →
  List A → ℚ
orderedOffDiagonalM2 C [] = 0ℚ
orderedOffDiagonalM2 C (head ∷ rest) =
  rowM2 C head rest
  + columnM2 C rest head
  + orderedOffDiagonalM2 C rest

------------------------------------------------------------------------
-- 3. Cardinality-free monotone fold.
------------------------------------------------------------------------

rowBelowM2 :
  ∀ {A} →
  (C : OrderedOffDiagonalR571Correspondence A) →
  (left : A) →
  (rest : List A) →
  R539.rowSum (pairScalar C) left rest
  ≤ rowM2 C left rest
rowBelowM2 C left [] = ℚP.≤-refl
rowBelowM2 C left (right ∷ rest) =
  ℚP.+-mono-≤
    (pairBelowPreferredM2 C left right)
    (rowBelowM2 C left rest)

columnBelowM2 :
  ∀ {A} →
  (C : OrderedOffDiagonalR571Correspondence A) →
  (rest : List A) →
  (right : A) →
  R539.columnSum (pairScalar C) rest right
  ≤ columnM2 C rest right
columnBelowM2 C [] right = ℚP.≤-refl
columnBelowM2 C (left ∷ rest) right =
  ℚP.+-mono-≤
    (pairBelowPreferredM2 C left right)
    (columnBelowM2 C rest right)

orderedOffDiagonalBelowM2 :
  ∀ {A} →
  (C : OrderedOffDiagonalR571Correspondence A) →
  (items : List A) →
  R539.orderedOffDiagonalSum (pairScalar C) items
  ≤ orderedOffDiagonalM2 C items
orderedOffDiagonalBelowM2 C [] = ℚP.≤-refl
orderedOffDiagonalBelowM2 C (head ∷ rest) =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (rowBelowM2 C head rest)
      (columnBelowM2 C rest head))
    (orderedOffDiagonalBelowM2 C rest)

------------------------------------------------------------------------
-- 4. Status / corrected trust cut.
------------------------------------------------------------------------

r540OrderedOffDiagonalM2CompilerClosed : Bool
r540OrderedOffDiagonalM2CompilerClosed = true

r540OrderedOffDiagonalM2IntroducesCardinalityTax : Bool
r540OrderedOffDiagonalM2IntroducesCardinalityTax = false

r567FullSquarePointwiseM2IsCanonicalConsumer : Bool
r567FullSquarePointwiseM2IsCanonicalConsumer = false

physicalR540PairToR571SampleSameObjectClosedHere : Bool
physicalR540PairToR571SampleSameObjectClosedHere = false

r540OrderedOffDiagonalM2CompilerClosedIsTrue :
  r540OrderedOffDiagonalM2CompilerClosed ≡ true
r540OrderedOffDiagonalM2CompilerClosedIsTrue = refl

r540OrderedOffDiagonalM2IntroducesCardinalityTaxIsFalse :
  r540OrderedOffDiagonalM2IntroducesCardinalityTax ≡ false
r540OrderedOffDiagonalM2IntroducesCardinalityTaxIsFalse = refl

r567FullSquarePointwiseM2IsCanonicalConsumerIsFalse :
  r567FullSquarePointwiseM2IsCanonicalConsumer ≡ false
r567FullSquarePointwiseM2IsCanonicalConsumerIsFalse = refl
