module DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact where

------------------------------------------------------------------------
-- GENERIC RECIPROCAL-SQUARE CANCELLATION
--
-- If x>0, 0<=q<1 and
--
--   q*x^2 < (1-q)^2,
--
-- then constructively
--
--   q*(1-q)^(-2) < x^(-2).
--
-- This is independent of how q was constructed (negative exponential,
-- cubic translation factor, or another geometric majorant).
------------------------------------------------------------------------

open import Data.Sum.Base using (inj₂)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as Identity
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Geometric
open import DASHI.Physics.YangMills.CompactLieProofLevel

inverse :
  (value : BishopReal.ℝ) → BishopReal._≄0 value → BishopReal.ℝ
inverse = BishopInverse._⁻¹

inverseSquare :
  (value : BishopReal.ℝ) →
  (nonzero : BishopReal._≄0 value) → BishopReal.ℝ
inverseSquare value nonzero =
  BishopReal._*_
    (inverse value nonzero)
    (inverse value nonzero)

xNonzero :
  ∀ {x} → BishopReal._<_ BishopReal.0ℝ x → BishopReal._≄0 x
xNonzero xPositive = inj₂ xPositive

gapPositive :
  ∀ {q} → Geometric.BishopUnitIntervalRatio q →
  BishopReal._<_ BishopReal.0ℝ (Identity.oneMinus q)
gapPositive inputs = Geometric.oneMinusPositive inputs

gapNonzero :
  ∀ {q} (inputs : Geometric.BishopUnitIntervalRatio q) →
  BishopReal._≄0 (Identity.oneMinus q)
gapNonzero inputs = inj₂ (gapPositive inputs)

inversePositive :
  ∀ {value} (nonzero : BishopReal._≄0 value) →
  BishopReal._<_ BishopReal.0ℝ value →
  BishopReal.Positive (inverse value nonzero)
inversePositive nonzero positive =
  BishopP.0<x⇒posx (BishopInverse.0<x⇒0<x⁻¹ nonzero positive)

inverseSquarePositive :
  ∀ {value} (nonzero : BishopReal._≄0 value) →
  BishopReal._<_ BishopReal.0ℝ value →
  BishopReal.Positive (inverseSquare value nonzero)
inverseSquarePositive nonzero positive =
  BishopP.posx,y⇒posx*y
    (inversePositive nonzero positive)
    (inversePositive nonzero positive)

square : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value

inverseSquareCancelsSquare :
  (value : BishopReal.ℝ) →
  (nonzero : BishopReal._≄0 value) →
  BishopReal._≃_
    (BishopReal._*_
      (inverseSquare value nonzero)
      (square value))
    BishopReal.1ℝ
inverseSquareCancelsSquare value nonzero =
  let
    inv = inverse value nonzero
    inverseLaw = BishopInverse.*-inverseˡ value nonzero
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 2
      (λ i v → (i ⊗ i) ⊗ (v ⊗ v)
        ⊜ (i ⊗ v) ⊗ (i ⊗ v))
      BishopP.≃-refl inv value)
    (BishopP.≃-trans
      (BishopP.*-cong inverseLaw inverseLaw)
      (BishopP.*-identityˡ BishopReal.1ℝ))

reciprocalSquareFromCross :
  ∀ {x q} →
  (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  (ratio : Geometric.BishopUnitIntervalRatio q) →
  BishopReal._<_
    (BishopReal._*_ q (square x))
    (square (Identity.oneMinus q)) →
  BishopReal._<_
    (BishopReal._*_
      q
      (inverseSquare (Identity.oneMinus q) (gapNonzero ratio)))
    (inverseSquare x (xNonzero xPositive))
reciprocalSquareFromCross {x} {q} xPositive ratio cross =
  let
    invX2 = inverseSquare x (xNonzero xPositive)
    invGap2 =
      inverseSquare (Identity.oneMinus q) (gapNonzero ratio)

    firstScaled =
      BishopP.*-monoʳ-<-pos
        (inverseSquarePositive
          (xNonzero xPositive) xPositive)
        cross

    leftCancel :
      BishopReal._≃_
        (BishopReal._*_
          invX2
          (BishopReal._*_ q (square x)))
        q
    leftCancel =
      let open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 3
          (λ i q′ x′ →
            i ⊗ (q′ ⊗ (x′ ⊗ x′))
            ⊜ q′ ⊗ (i ⊗ (x′ ⊗ x′)))
          BishopP.≃-refl invX2 q x)
        (BishopP.≃-trans
          (BishopP.*-congˡ
            (inverseSquareCancelsSquare x (xNonzero xPositive)))
          (BishopP.*-identityʳ q))

    qBelowInvXGapSquare :
      BishopReal._<_
        q
        (BishopReal._*_
          invX2 (square (Identity.oneMinus q)))
    qBelowInvXGapSquare =
      BishopP.<-respˡ-≃ leftCancel firstScaled

    secondScaled =
      BishopP.*-monoʳ-<-pos
        (inverseSquarePositive
          (gapNonzero ratio) (gapPositive ratio))
        qBelowInvXGapSquare

    leftCommute :
      BishopReal._≃_
        (BishopReal._*_ invGap2 q)
        (BishopReal._*_ q invGap2)
    leftCommute = BishopP.*-comm invGap2 q

    rightCancel :
      BishopReal._≃_
        (BishopReal._*_
          invGap2
          (BishopReal._*_ invX2 (square (Identity.oneMinus q))))
        invX2
    rightCancel =
      let open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 3
          (λ g i v → g ⊗ (i ⊗ v)
            ⊜ i ⊗ (g ⊗ v))
          BishopP.≃-refl
          invGap2 invX2 (square (Identity.oneMinus q)))
        (BishopP.≃-trans
          (BishopP.*-congˡ
            (inverseSquareCancelsSquare
              (Identity.oneMinus q) (gapNonzero ratio)))
          (BishopP.*-identityʳ invX2))
  in
  BishopP.<-respʳ-≃ rightCancel
    (BishopP.<-respˡ-≃ leftCommute secondScaled)

bishopGeometricReciprocalSquareFromCrossLevel : ProofLevel
bishopGeometricReciprocalSquareFromCrossLevel = machineChecked
