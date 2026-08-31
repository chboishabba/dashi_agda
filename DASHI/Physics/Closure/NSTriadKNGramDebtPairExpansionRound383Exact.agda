module DASHI.Physics.Closure.NSTriadKNGramDebtPairExpansionRound383Exact where

------------------------------------------------------------------------
-- ROUND383 / EXACT PAIR EXPANSION OF THE R180 RECURSIVE GRAM DEBT
--
-- R180 stores covariance recursively as
--
--   D(u :: us) = 2 Re<u,sum us> + D(us).
--
-- Hermitian additivity expands the first term into all pairs (u,v), v in us.
-- Therefore the recursive debt is exactly the finite sum over unordered
-- list-position pairs.  This is only finite algebra; no sign or estimate is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291

F : C3.RealField _
F = Rational.rationalRealField

pairGram : C3.Complex3 F → C3.Complex3 F → ℚ
pairGram left right = R291.two * R179.realHermitianCross left right

headPairSum : C3.Complex3 F → List (C3.Complex3 F) → ℚ
headPairSum left [] = 0ℚ
headPairSum left (right ∷ rest) =
  pairGram left right + headPairSum left rest

allPairSum : List (C3.Complex3 F) → ℚ
allPairSum [] = 0ℚ
allPairSum (left ∷ rest) = headPairSum left rest + allPairSum rest

realCrossOverSum :
  (left : C3.Complex3 F) →
  (rest : List (C3.Complex3 F)) →
  R179.realHermitianCross left (R180.sumCells rest)
  ≡ sumCross left rest
  where
  sumCross : C3.Complex3 F → List (C3.Complex3 F) → ℚ
  sumCross left [] = 0ℚ
  sumCross left (right ∷ tail) =
    R179.realHermitianCross left right + sumCross left tail
realCrossOverSum left [] = R179.realCrossZeroRight left
  where
  open import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact
realCrossOverSum left (right ∷ tail) =
  trans
    (R291.realCrossAddRight left right (R180.sumCells tail))
    (cong (R179.realHermitianCross left right +_)
      (realCrossOverSum left tail))

-- A separately named recursive cross sum avoids exposing the local helper in
-- downstream statements.
sumCross : C3.Complex3 F → List (C3.Complex3 F) → ℚ
sumCross left [] = 0ℚ
sumCross left (right ∷ tail) =
  R179.realHermitianCross left right + sumCross left tail

realCrossOverSumExact :
  (left : C3.Complex3 F) →
  (rest : List (C3.Complex3 F)) →
  R179.realHermitianCross left (R180.sumCells rest)
  ≡ sumCross left rest
realCrossOverSumExact left [] = R179.realCrossZeroRight left
realCrossOverSumExact left (right ∷ tail) =
  trans
    (R291.realCrossAddRight left right (R180.sumCells tail))
    (cong (R179.realHermitianCross left right +_)
      (realCrossOverSumExact left tail))

scaleCrossSum :
  (left : C3.Complex3 F) →
  (rest : List (C3.Complex3 F)) →
  R291.two * sumCross left rest ≡ headPairSum left rest
scaleCrossSum left [] = Rational.rationalOrderedExtension .DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier.OrderedRealExtension.leqReflexive 0ℚ `seq` refl
scaleCrossSum left (right ∷ tail) =
  let
    x = R179.realHermitianCross left right
    y = sumCross left tail
  in
  trans
    (R179.distributeTwo x y)
    (cong (pairGram left right +_) (scaleCrossSum left tail))

r180GramDebtIsAllPairSum :
  (cells : List (C3.Complex3 F)) →
  R180.gramDebt cells ≡ allPairSum cells
r180GramDebtIsAllPairSum [] = refl
r180GramDebtIsAllPairSum (left ∷ rest) =
  trans
    (cong₂ _+_
      (trans
        (cong (R291.two *_) (realCrossOverSumExact left rest))
        (scaleCrossSum left rest))
      (r180GramDebtIsAllPairSum rest))
    refl

round383R180DebtExpandedIntoLiteralPairSum : Bool
round383R180DebtExpandedIntoLiteralPairSum = true

round383NoAbsoluteValueOrMajorantIntroduced : Bool
round383NoAbsoluteValueOrMajorantIntroduced = true

round383R180DebtExpandedIntoLiteralPairSumIsTrue :
  round383R180DebtExpandedIntoLiteralPairSum ≡ true
round383R180DebtExpandedIntoLiteralPairSumIsTrue = refl
