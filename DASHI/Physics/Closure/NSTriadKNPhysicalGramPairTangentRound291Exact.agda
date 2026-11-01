module DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact where

------------------------------------------------------------------------
-- ROUND291 / TWO-CELL GRAM TANGENT, BEFORE FINITE ORBIT AGGREGATION
--
-- Work directly on the rational C^3 carrier used by R179/R227.  If two literal
-- mixed-helicity cells A,B have tangents
--
--   dA = -rhoA A + fA,
--   dB = -rhoB B + fB,
--
-- then for the real Hermitian Gram scalar
--
--   g(A,B) = 2 Re <A,B>
--
-- the product rule gives exactly
--
--   dg = -(rhoA+rhoB) g
--        + 2 Re <fA,B> + 2 Re <A,fB>.
--
-- This is the physical algebra required by R290.  No sign of the nonlinear
-- remainder is assumed.
--
-- The sole upstream physical weld left after this lemma is to prove that the
-- ACTUAL R224/R227 cell tangent, obtained from the Round240 Galerkin equation,
-- has rhoA = nu(|p|^2+|q|^2) and fA equal to the literal R230 product-rule
-- nonlinear cell.  That is a same-object linearity/derivative theorem, not a
-- new covariance estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

realScale : ℚ → C3.Complex3 F → C3.Complex3 F
realScale scalar value = C3.complex3Scale (C3.realEmbed F scalar) value

scaledRealCrossLeft :
  (scalar : ℚ) (u v : C3.Complex3 F) →
  R179.realHermitianCross (realScale scalar u) v
  ≡ scalar * R179.realHermitianCross u v
scaledRealCrossLeft scalar
    (C3.complex3
      (C3.complex ur ui) (C3.complex vr vi) (C3.complex wr wi))
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (scalar ∷ ur ∷ ui ∷ vr ∷ vi ∷ wr ∷ wi ∷ xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

scaledRealCrossRight :
  (scalar : ℚ) (u v : C3.Complex3 F) →
  R179.realHermitianCross u (realScale scalar v)
  ≡ scalar * R179.realHermitianCross u v
scaledRealCrossRight scalar
    (C3.complex3
      (C3.complex ur ui) (C3.complex vr vi) (C3.complex wr wi))
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (scalar ∷ ur ∷ ui ∷ vr ∷ vi ∷ wr ∷ wi ∷ xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

realCrossAddLeft :
  (a b c : C3.Complex3 F) →
  R179.realHermitianCross (C3.complex3Add a b) c
  ≡ R179.realHermitianCross a c + R179.realHermitianCross b c
realCrossAddLeft
    (C3.complex3
      (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci))
    (C3.complex3
      (C3.complex dr di) (C3.complex er ei) (C3.complex fr fi))
    (C3.complex3
      (C3.complex gr gi) (C3.complex hr hi) (C3.complex ir ii)) =
  solve
    (ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci ∷ dr ∷ di ∷ er ∷ ei ∷ fr ∷ fi
      ∷ gr ∷ gi ∷ hr ∷ hi ∷ ir ∷ ii ∷ [])

realCrossAddRight :
  (a b c : C3.Complex3 F) →
  R179.realHermitianCross a (C3.complex3Add b c)
  ≡ R179.realHermitianCross a b + R179.realHermitianCross a c
realCrossAddRight
    (C3.complex3
      (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci))
    (C3.complex3
      (C3.complex dr di) (C3.complex er ei) (C3.complex fr fi))
    (C3.complex3
      (C3.complex gr gi) (C3.complex hr hi) (C3.complex ir ii)) =
  solve
    (ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci ∷ dr ∷ di ∷ er ∷ ei ∷ fr ∷ fi
      ∷ gr ∷ gi ∷ hr ∷ hi ∷ ir ∷ ii ∷ [])

record DampedCellPair : Set where
  constructor damped-cell-pair
  field
    cellA cellB tangentA tangentB forcingA forcingB : C3.Complex3 F
    rateA rateB : ℚ

    tangentALaw :
      tangentA ≡ C3.complex3Add (realScale (0ℚ - rateA) cellA) forcingA

    tangentBLaw :
      tangentB ≡ C3.complex3Add (realScale (0ℚ - rateB) cellB) forcingB

open DampedCellPair public

gram : DampedCellPair → ℚ
gram P = two * R179.realHermitianCross (cellA P) (cellB P)

gramTangent : DampedCellPair → ℚ
gramTangent P =
  two *
    (R179.realHermitianCross (tangentA P) (cellB P)
      + R179.realHermitianCross (cellA P) (tangentB P))

nonlinearGramRemainder : DampedCellPair → ℚ
nonlinearGramRemainder P =
  two *
    (R179.realHermitianCross (forcingA P) (cellB P)
      + R179.realHermitianCross (cellA P) (forcingB P))

pairRate : DampedCellPair → ℚ
pairRate P = rateA P + rateB P

gramPairDampedTangent :
  (P : DampedCellPair) →
  gramTangent P
  ≡ (0ℚ - pairRate P) * gram P + nonlinearGramRemainder P
gramPairDampedTangent P rewrite tangentALaw P | tangentBLaw P =
  let
    a = cellA P
    b = cellB P
    fa = forcingA P
    fb = forcingB P
    ra = rateA P
    rb = rateB P

    leftExpansion :
      R179.realHermitianCross
        (C3.complex3Add (realScale (0ℚ - ra) a) fa) b
      ≡ (0ℚ - ra) * R179.realHermitianCross a b
          + R179.realHermitianCross fa b
    leftExpansion = trans
      (realCrossAddLeft (realScale (0ℚ - ra) a) fa b)
      (cong₂ _+_ (scaledRealCrossLeft (0ℚ - ra) a b) refl)

    rightExpansion :
      R179.realHermitianCross a
        (C3.complex3Add (realScale (0ℚ - rb) b) fb)
      ≡ (0ℚ - rb) * R179.realHermitianCross a b
          + R179.realHermitianCross a fb
    rightExpansion = trans
      (realCrossAddRight a (realScale (0ℚ - rb) b) fb)
      (cong₂ _+_ (scaledRealCrossRight (0ℚ - rb) a b) refl)
  in
  trans
    (cong (two *_) (cong₂ _+_ leftExpansion rightExpansion))
    (solve
      (ra ∷ rb ∷ R179.realHermitianCross a b
        ∷ R179.realHermitianCross fa b
        ∷ R179.realHermitianCross a fb ∷ []))

round291DampedTwoCellGramTangentClosed : Bool
round291DampedTwoCellGramTangentClosed = true

round291NonlinearRemainderSignAssumed : Bool
round291NonlinearRemainderSignAssumed = false

round291ActualR227CellTangentWeldClosed : Bool
round291ActualR227CellTangentWeldClosed = false

round291FiniteOffDiagonalAggregationClosed : Bool
round291FiniteOffDiagonalAggregationClosed = false

round291R222BudgetClosed : Bool
round291R222BudgetClosed = false

round291PackageAClosed : Bool
round291PackageAClosed = false

round291ClayPromotion : Bool
round291ClayPromotion = false

round291DampedTwoCellGramTangentClosedIsTrue :
  round291DampedTwoCellGramTangentClosed ≡ true
round291DampedTwoCellGramTangentClosedIsTrue = refl
