module DASHI.Foundations.BishopCubicTranslationGeometricRatioExact where

------------------------------------------------------------------------
-- CUBIC TRANSLATION GEOMETRIC RATIO
--
-- Let
--
--   D3(x) = 1 + x + x^2/2 + x^3/6,
--   q(x)  = D3(x)^(-1).
--
-- For every x>0 we prove constructively:
--
--   0 < q(x) < 1,
--   q(x) * x^2 < (1-q(x))^2.
--
-- The algebraic core is
--
--   (D3(x)-1)^2 - D3(x)x^2 = x^4(x^2+3)/36 > 0.
--
-- This is the scalar kernel needed by the Erdős cubic-translation route and
-- avoids any small-x restriction or global exp-additivity theorem.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (0ℚᵘ; 1ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Sum.Base using (inj₂)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialCubicTranslationLowerExact as Cubic
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Geometric
open import DASHI.Physics.YangMills.CompactLieProofLevel

half oneSixth oneThirtySixth three : BishopReal.ℝ
half = Exp.embed (+ 1 / 2)
oneSixth = Exp.embed (+ 1 / 6)
oneThirtySixth = Exp.embed (+ 1 / 36)
three = Exp.embed (+ 3 / 1)

square fourth : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value
fourth value = BishopReal._*_ (square value) (square value)

d3 : BishopReal.ℝ → BishopReal.ℝ
d3 = Cubic.cubicTranslationFactor

d3Gap : BishopReal.ℝ → BishopReal.ℝ
d3Gap x = BishopReal._-_ (d3 x) BishopReal.1ℝ

onePositive : BishopReal._<_ BishopReal.0ℝ BishopReal.1ℝ
onePositive =
  BishopP.p<q⇒p⋆<q⋆
    0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ 1ℚᵘ)

oneNonzero : BishopReal._≄0 BishopReal.1ℝ
oneNonzero = inj₂ onePositive

halfNonnegative oneSixthNonnegative : BishopReal.NonNegative _
halfNonnegative =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆
      0ℚᵘ (+ 1 / 2) (ℚP.nonNegative⁻¹ (+ 1 / 2)))
oneSixthNonnegative =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆
      0ℚᵘ (+ 1 / 6) (ℚP.nonNegative⁻¹ (+ 1 / 6)))

oneThirtySixthPositive : BishopReal.Positive oneThirtySixth
oneThirtySixthPositive =
  BishopP.posp⇒posp⋆ (+ 1 / 36) (ℚP.positive⁻¹ (+ 1 / 36))

threePositive : BishopReal.Positive three
threePositive =
  BishopP.posp⇒posp⋆ (+ 3 / 1) (ℚP.positive⁻¹ (+ 3 / 1))

squareNonnegative :
  ∀ {x} → BishopReal._<_ BishopReal.0ℝ x →
  BishopReal.NonNegative (square x)
squareNonnegative xPositive =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopP.pos⇒nonNeg (BishopP.0<x⇒posx xPositive))
    (BishopP.pos⇒nonNeg (BishopP.0<x⇒posx xPositive))

cubeNonnegative :
  ∀ {x} → BishopReal._<_ BishopReal.0ℝ x →
  BishopReal.NonNegative (Cubic.cube x)
cubeNonnegative xPositive =
  BishopP.nonNegx,y⇒nonNegx*y
    (squareNonnegative xPositive)
    (BishopP.pos⇒nonNeg (BishopP.0<x⇒posx xPositive))

positiveTail : BishopReal.ℝ → BishopReal.ℝ
positiveTail x =
  BishopReal._+_
    (BishopReal._+_ x (BishopReal._*_ half (square x)))
    (BishopReal._*_ oneSixth (Cubic.cube x))

positiveTailPositive :
  ∀ {x} → BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ BishopReal.0ℝ (positiveTail x)
positiveTailPositive {x} xPositive =
  let
    squarePartNN =
      BishopP.nonNegx,y⇒nonNegx*y
        halfNonnegative (squareNonnegative xPositive)
    cubePartNN =
      BishopP.nonNegx,y⇒nonNegx*y
        oneSixthNonnegative (cubeNonnegative xPositive)
    xBelowFirst =
      BishopP.≤-respˡ-≃
        (BishopP.≃-symm (BishopP.+-identityʳ x))
        (BishopP.+-monoʳ-≤ x (BishopP.nonNegx⇒0≤x squarePartNN))
    zeroBelowFirst = BishopP.<-≤-trans xPositive xBelowFirst
    firstBelowTail =
      BishopP.≤-respˡ-≃
        (BishopP.≃-symm
          (BishopP.+-identityʳ
            (BishopReal._+_ x (BishopReal._*_ half (square x)))))
        (BishopP.+-monoʳ-≤
          (BishopReal._+_ x (BishopReal._*_ half (square x)))
          (BishopP.nonNegx⇒0≤x cubePartNN))
  in
  BishopP.<-≤-trans zeroBelowFirst firstBelowTail

d3IsOnePlusTail :
  ∀ x → BishopReal._≃_ (d3 x)
    (BishopReal._+_ BishopReal.1ℝ (positiveTail x))
d3IsOnePlusTail x =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ x′ →
      (((Κ 1ℚᵘ ⊕ x′)
         ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
         ⊕ (Κ (+ 1 / 6) ⊗ ((x′ ⊗ x′) ⊗ x′)))
      ⊜ Κ 1ℚᵘ ⊕
          ((x′ ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
           ⊕ (Κ (+ 1 / 6) ⊗ ((x′ ⊗ x′) ⊗ x′))))
    BishopP.≃-refl x

d3AboveOne :
  ∀ {x} → BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ BishopReal.1ℝ (d3 x)
d3AboveOne {x} xPositive =
  BishopP.<-respʳ-≃
    (BishopP.≃-symm (d3IsOnePlusTail x))
    (BishopP.+-monoʳ-< BishopReal.1ℝ
      (positiveTailPositive xPositive))

d3Positive :
  ∀ {x} → BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ BishopReal.0ℝ (d3 x)
d3Positive xPositive =
  BishopP.<-trans onePositive (d3AboveOne xPositive)

d3Nonzero :
  ∀ {x} → BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._≄0 (d3 x)
d3Nonzero xPositive = inj₂ (d3Positive xPositive)

q : (x : BishopReal.ℝ) →
  BishopReal._<_ BishopReal.0ℝ x → BishopReal.ℝ
q x xPositive = BishopInverse._⁻¹ (d3 x) (d3Nonzero xPositive)

qPositive :
  ∀ {x} (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  BishopReal._<_ BishopReal.0ℝ (q x xPositive)
qPositive xPositive =
  BishopInverse.0<x⇒0<x⁻¹
    (d3Nonzero xPositive) (d3Positive xPositive)

inverseOneIsOne :
  BishopReal._≃_
    (BishopInverse._⁻¹ BishopReal.1ℝ oneNonzero)
    BishopReal.1ℝ
inverseOneIsOne =
  BishopP.≃-symm
    (BishopInverse.⁻¹-unique
      BishopReal.1ℝ BishopReal.1ℝ oneNonzero
      (BishopP.*-identityʳ BishopReal.1ℝ))

qBelowOne :
  ∀ {x} (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  BishopReal._<_ (q x xPositive) BishopReal.1ℝ
qBelowOne {x} xPositive =
  BishopP.<-respʳ-≃ inverseOneIsOne
    (BishopInverse.x<y∧posx,y⇒y⁻¹<x⁻¹
      (d3AboveOne xPositive)
      oneNonzero
      (d3Nonzero xPositive)
      (BishopP.0<x⇒posx onePositive)
      (BishopP.0<x⇒posx (d3Positive xPositive)))

cubicRatioInputs :
  ∀ {x} (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  Geometric.BishopUnitIntervalRatio (q x xPositive)
cubicRatioInputs xPositive = record
  { ratioNonnegative = BishopP.<⇒≤ (qPositive xPositive)
  ; ratioBelowOne = qBelowOne xPositive
  }

crossFactorization :
  ∀ x →
  BishopReal._≃_
    (BishopReal._-_
      (square (d3Gap x))
      (BishopReal._*_ (d3 x) (square x)))
    (BishopReal._*_
      oneThirtySixth
      (BishopReal._*_
        (fourth x)
        (BishopReal._+_ (square x) three)))
crossFactorization x =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ x′ →
      (((((((Κ 1ℚᵘ ⊕ x′)
              ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
              ⊕ (Κ (+ 1 / 6) ⊗ ((x′ ⊗ x′) ⊗ x′)))
             ⊖ Κ 1ℚᵘ)
            ⊗
            (((((Κ 1ℚᵘ ⊕ x′)
              ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
              ⊕ (Κ (+ 1 / 6) ⊗ ((x′ ⊗ x′) ⊗ x′)))
             ⊖ Κ 1ℚᵘ))
          ⊖
          (((((Κ 1ℚᵘ ⊕ x′)
              ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
              ⊕ (Κ (+ 1 / 6) ⊗ ((x′ ⊗ x′) ⊗ x′)))
             ⊗ (x′ ⊗ x′))))
      ⊜ Κ (+ 1 / 36) ⊗
          (((x′ ⊗ x′) ⊗ (x′ ⊗ x′))
           ⊗ ((x′ ⊗ x′) ⊕ Κ (+ 3 / 1))))
    BishopP.≃-refl x

crossDifferencePositive :
  ∀ {x} → BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ BishopReal.0ℝ
    (BishopReal._-_
      (square (d3Gap x))
      (BishopReal._*_ (d3 x) (square x)))
crossDifferencePositive {x} xPositive =
  let
    xp = BishopP.0<x⇒posx xPositive
    x2p = BishopP.posx,y⇒posx*y xp xp
    x4p = BishopP.posx,y⇒posx*y x2p x2p
    x2plus3p =
      BishopP.0<x⇒posx
        (BishopP.<-≤-trans
          (BishopP.posx⇒0<x threePositive)
          (BishopP.≤-respˡ-≃
            (BishopP.≃-symm (BishopP.+-identityˡ three))
            (BishopP.+-monoˡ-≤ three
              (BishopP.nonNegx⇒0≤x
                (BishopP.pos⇒nonNeg x2p)))))
    rhsPositive =
      BishopP.posx⇒0<x
        (BishopP.posx,y⇒posx*y
          oneThirtySixthPositive
          (BishopP.posx,y⇒posx*y x4p x2plus3p))
  in
  BishopP.<-respʳ-≃
    (BishopP.≃-symm (crossFactorization x))
    rhsPositive

d3CrossInequality :
  ∀ {x} → BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_
    (BishopReal._*_ (d3 x) (square x))
    (square (d3Gap x))
d3CrossInequality {x} xPositive =
  BishopP.0<y-x⇒x<y
    (BishopReal._*_ (d3 x) (square x))
    (square (d3Gap x))
    (crossDifferencePositive xPositive)

------------------------------------------------------------------------
-- Scale the D3 inequality by q^2.  Since q*D3=1 this becomes exactly
--
--   q*x^2 < (1-q)^2.

qCrossInequality :
  ∀ {x} (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  BishopReal._<_
    (BishopReal._*_ (q x xPositive) (square x))
    (square (BishopReal._-_ BishopReal.1ℝ (q x xPositive)))
qCrossInequality {x} xPositive =
  let
    qx = q x xPositive
    d = d3 x
    q2 = square qx
    q2Positive =
      BishopP.posx,y⇒posx*y
        (BishopP.0<x⇒posx (qPositive xPositive))
        (BishopP.0<x⇒posx (qPositive xPositive))
    scaled =
      BishopP.*-monoʳ-<-pos
        q2Positive
        (d3CrossInequality xPositive)
    inverseLaw =
      BishopInverse.*-inverseˡ d (d3Nonzero xPositive)
    leftNormalize :
      BishopReal._≃_
        (BishopReal._*_ q2 (BishopReal._*_ d (square x)))
        (BishopReal._*_ qx (square x))
    leftNormalize =
      let open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 3
          (λ q′ d′ x2 →
            (q′ ⊗ q′) ⊗ (d′ ⊗ x2)
            ⊜ (q′ ⊗ d′) ⊗ (q′ ⊗ x2))
          BishopP.≃-refl qx d (square x))
        (BishopP.≃-trans
          (BishopP.*-congʳ inverseLaw)
          (BishopP.*-identityˡ (BishopReal._*_ qx (square x))))
    rightNormalize :
      BishopReal._≃_
        (BishopReal._*_ q2 (square (d3Gap x)))
        (square (BishopReal._-_ BishopReal.1ℝ qx))
    rightNormalize =
      let open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 2
          (λ q′ d′ →
            (q′ ⊗ q′) ⊗ ((d′ ⊖ Κ 1ℚᵘ) ⊗ (d′ ⊖ Κ 1ℚᵘ))
            ⊜ ((q′ ⊗ d′) ⊖ q′) ⊗ ((q′ ⊗ d′) ⊖ q′))
          BishopP.≃-refl qx d)
        (BishopP.*-cong
          (BishopP.+-cong inverseLaw (BishopP.≃-refl))
          (BishopP.+-cong inverseLaw (BishopP.≃-refl)))
  in
  BishopP.<-respʳ-≃ rightNormalize
    (BishopP.<-respˡ-≃ leftNormalize scaled)

bishopCubicTranslationGeometricRatioLevel : ProofLevel
bishopCubicTranslationGeometricRatioLevel = machineChecked
