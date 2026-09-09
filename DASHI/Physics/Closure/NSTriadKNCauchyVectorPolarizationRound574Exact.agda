module DASHI.Physics.Closure.NSTriadKNCauchyVectorPolarizationRound574Exact where

------------------------------------------------------------------------
-- ROUND574 / R446 CAUCHY PSD -> MIXED VECTOR FULL-SQUARE POLARIZATION
--
-- A positive-rate cell stores two vectors G,D at the same rate.  R446 applied
-- to G-D gives a nonnegative exact Cauchy quadratic.  R573 then yields
--
--   2 B_K(G,D) <= Q_K(G) + Q_K(D)
--
-- on the complete finite square, without absolute values or heat/Laplace.
-- This is finite algebra only: whether Q_K(G),Q_K(D) are cheaper analytic
-- objects is deliberately left for the next BIDI adequacy audit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _+_; _*_; _-_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNRationalCauchySchurComplementRound443Exact as R443
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNCauchyPolarizationUpperRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

record CauchyVectorPairCell574 : Set where
  constructor cauchy-vector-pair-cell-574
  field
    rate574 : ℚ
    left574 : C3.Complex3 F
    right574 : C3.Complex3 F
    ratePositive574 : Positive rate574

open CauchyVectorPairCell574 public

kernel574 : CauchyVectorPairCell574 → CauchyVectorPairCell574 → ℚ
kernel574 a b = R443.cauchyEntry (rate574 a) (rate574 b)

leftPair574 rightPair574 mixedPair574 differencePair574 :
  CauchyVectorPairCell574 → CauchyVectorPairCell574 → ℚ
leftPair574 a b = kernel574 a b * R179.realHermitianCross (left574 a) (left574 b)
rightPair574 a b = kernel574 a b * R179.realHermitianCross (right574 a) (right574 b)
mixedPair574 a b = kernel574 a b * R179.realHermitianCross (left574 a) (right574 b)
differencePair574 a b =
  kernel574 a b *
    R179.realHermitianCross
      (C3.complex3Subtract (left574 a) (right574 a))
      (C3.complex3Subtract (left574 b) (right574 b))

crossSubtractBoth574 :
  (a b c d : C3.Complex3 F) →
  R179.realHermitianCross (C3.complex3Subtract a b) (C3.complex3Subtract c d)
  ≡ R179.realHermitianCross a c + R179.realHermitianCross b d
      - R179.realHermitianCross a d - R179.realHermitianCross b c
crossSubtractBoth574
    (C3.complex3 (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci))
    (C3.complex3 (C3.complex dr di) (C3.complex er ei) (C3.complex fr fi))
    (C3.complex3 (C3.complex gr gi) (C3.complex hr hi) (C3.complex ir ii))
    (C3.complex3 (C3.complex jr ji) (C3.complex kr ki) (C3.complex lr li)) =
  solve
    (ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci ∷ dr ∷ di ∷ er ∷ ei ∷ fr ∷ fi
    ∷ gr ∷ gi ∷ hr ∷ hi ∷ ir ∷ ii ∷ jr ∷ ji ∷ kr ∷ ki ∷ lr ∷ li ∷ [])

differencePairIsPolarized574 :
  (a b : CauchyVectorPairCell574) →
  differencePair574 a b
  ≡ R573.polarizedPair573 leftPair574 rightPair574 mixedPair574 a b
differencePairIsPolarized574 a b
  rewrite crossSubtractBoth574
    (left574 a) (right574 a) (left574 b) (right574 b) =
  solve
    (kernel574 a b
    ∷ R179.realHermitianCross (left574 a) (left574 b)
    ∷ R179.realHermitianCross (right574 a) (right574 b)
    ∷ R179.realHermitianCross (left574 a) (right574 b)
    ∷ R179.realHermitianCross (right574 a) (left574 b) ∷ [])

rowPolarizedPointwise574 :
  (x : CauchyVectorPairCell574) (xs : List CauchyVectorPairCell574) →
  R539.rowSum differencePair574 x xs
  ≡ R539.rowSum
      (R573.polarizedPair573 leftPair574 rightPair574 mixedPair574) x xs
rowPolarizedPointwise574 x [] = refl
rowPolarizedPointwise574 x (y ∷ ys) =
  cong₂ _+_ (differencePairIsPolarized574 x y) (rowPolarizedPointwise574 x ys)

columnPolarizedPointwise574 :
  (xs : List CauchyVectorPairCell574) (x : CauchyVectorPairCell574) →
  R539.columnSum differencePair574 xs x
  ≡ R539.columnSum
      (R573.polarizedPair573 leftPair574 rightPair574 mixedPair574) xs x
columnPolarizedPointwise574 [] x = refl
columnPolarizedPointwise574 (y ∷ ys) x =
  cong₂ _+_ (differencePairIsPolarized574 y x) (columnPolarizedPointwise574 ys x)

differencePairIsPolarizedFull574 :
  (items : List CauchyVectorPairCell574) →
  R543.fullSquareSum differencePair574 items
  ≡ R543.fullSquareSum
      (R573.polarizedPair573 leftPair574 rightPair574 mixedPair574) items
differencePairIsPolarizedFull574 [] = refl
differencePairIsPolarizedFull574 (head ∷ rest)
  rewrite differencePairIsPolarized574 head head
        | rowPolarizedPointwise574 head rest
        | columnPolarizedPointwise574 rest head
        | differencePairIsPolarizedFull574 rest = refl

pairSymmetric574 :
  (values : CauchyVectorPairCell574 → C3.Complex3 F) →
  (a b : CauchyVectorPairCell574) →
  kernel574 a b * R179.realHermitianCross (values a) (values b)
  ≡ kernel574 b a * R179.realHermitianCross (values b) (values a)
pairSymmetric574 values a b =
  cong₂ _*_
    (R443.cauchyEntrySymmetric (rate574 a) (rate574 b))
    (R287.realHermitianCrossSymmetric (values a) (values b))

toDifferenceCell574 : CauchyVectorPairCell574 → R446.PositiveRateComplex3Cell
toDifferenceCell574 cell =
  R446.positive-rate-complex3-cell
    (rate574 cell)
    (C3.complex3Subtract (left574 cell) (right574 cell))
    (ratePositive574 cell)

differenceCells574 : List CauchyVectorPairCell574 → List R446.PositiveRateComplex3Cell
differenceCells574 [] = []
differenceCells574 (cell ∷ rest) = toDifferenceCell574 cell ∷ differenceCells574 rest

mappedRow574 :
  (head : CauchyVectorPairCell574) (rest : List CauchyVectorPairCell574) →
  R539.rowSum differencePair574 head rest
  ≡ R446.hermitianRow (toDifferenceCell574 head) (differenceCells574 rest)
mappedRow574 head [] = refl
mappedRow574 head (cell ∷ rest) =
  cong₂ _+_ refl (mappedRow574 head rest)

mappedColumn574 :
  (rest : List CauchyVectorPairCell574) (head : CauchyVectorPairCell574) →
  R539.columnSum differencePair574 rest head
  ≡ R446.hermitianRow (toDifferenceCell574 head) (differenceCells574 rest)
mappedColumn574 [] head = refl
mappedColumn574 (cell ∷ rest) head =
  cong₂ _+_
    (pairSymmetric574
      (λ x → C3.complex3Subtract (left574 x) (right574 x)) cell head)
    (mappedColumn574 rest head)

fullDifferenceIsR446574 :
  (cells : List CauchyVectorPairCell574) →
  R543.fullSquareSum differencePair574 cells
  ≡ R446.hermitianCauchyForm (differenceCells574 cells)
fullDifferenceIsR446574 [] = refl
fullDifferenceIsR446574 (head ∷ rest)
  rewrite mappedRow574 head rest
        | mappedColumn574 rest head
        | fullDifferenceIsR446574 rest =
  solve
    (differencePair574 head head
    ∷ R446.hermitianRow (toDifferenceCell574 head) (differenceCells574 rest)
    ∷ R446.hermitianCauchyForm (differenceCells574 rest) ∷ [])

differenceFullNonnegative574 :
  (cells : List CauchyVectorPairCell574) →
  0ℚ ≤ R543.fullSquareSum differencePair574 cells
differenceFullNonnegative574 cells =
  subst (0ℚ ≤_) (sym (fullDifferenceIsR446574 cells))
    (R446.hermitianCauchyFormNonnegative (differenceCells574 cells))

polarizedFullNonnegative574 :
  (cells : List CauchyVectorPairCell574) →
  0ℚ ≤ R543.fullSquareSum
    (R573.polarizedPair573 leftPair574 rightPair574 mixedPair574) cells
polarizedFullNonnegative574 cells =
  subst (0ℚ ≤_) (differencePairIsPolarizedFull574 cells)
    (differenceFullNonnegative574 cells)

mixedCauchyPolarizationUpper574 :
  (cells : List CauchyVectorPairCell574) →
  R573.two573 * R543.fullSquareSum mixedPair574 cells
  ≤ R543.fullSquareSum leftPair574 cells + R543.fullSquareSum rightPair574 cells
mixedCauchyPolarizationUpper574 cells =
  R573.polarizationUpper573 leftPair574 rightPair574 mixedPair574 cells
    (polarizedFullNonnegative574 cells)

round574R446DifferencePSDReused : Bool
round574R446DifferencePSDReused = true

round574MixedCauchyPolarizationUpperClosed : Bool
round574MixedCauchyPolarizationUpperClosed = true

round574UsesAbsoluteValue : Bool
round574UsesAbsoluteValue = false

round574PositiveMajorantsCutoffUniformlyPaid : Bool
round574PositiveMajorantsCutoffUniformlyPaid = false

round574CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round574CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round574ClayPromotion : Bool
round574ClayPromotion = false

round574ClayPromotionIsFalse : round574ClayPromotion ≡ false
round574ClayPromotionIsFalse = refl
