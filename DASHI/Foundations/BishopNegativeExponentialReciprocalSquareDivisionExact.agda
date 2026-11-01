module DASHI.Foundations.BishopNegativeExponentialReciprocalSquareDivisionExact where

------------------------------------------------------------------------
-- DIVISION FORM OF THE NEGATIVE-EXPONENTIAL KERNEL
--
-- Cancel the positive squares in
--
--   exp(-x) * x^2 < (1-exp(-x))^2
--
-- to obtain
--
--   exp(-x) / (1-exp(-x))^2 < 1/x^2.
------------------------------------------------------------------------

open import Data.Rational.Unnormalised using (1ℚᵘ)
open import Data.Sum.Base using (inj₂)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopNegativeExponentialQuarticBracketExact as Bracket
import DASHI.Foundations.BishopNegativeExponentialUnitIntervalExact as Unit
import DASHI.Foundations.BishopNegativeExponentialReciprocalSquareExact as Cross
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
  ∀ {x} → Unit.PositiveUnitIntervalPoint x → BishopReal._≄0 x
xNonzero inputs = inj₂ (Unit.positive inputs)

qGapPositive :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal._<_ BishopReal.0ℝ (Cross.gap (Cross.q x))
qGapPositive inputs =
  BishopP.x<y⇒0<y-x
    (Cross.q _)
    BishopReal.1ℝ
    (Unit.negativeExpBelowOne inputs)

qGapNonzero :
  ∀ {x} → Unit.PositiveUnitIntervalPoint x →
  BishopReal._≄0 (Cross.gap (Cross.q x))
qGapNonzero inputs = inj₂ (qGapPositive inputs)

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

inverseSquareCancelsSquare :
  (value : BishopReal.ℝ) →
  (nonzero : BishopReal._≄0 value) →
  BishopReal._≃_
    (BishopReal._*_
      (inverseSquare value nonzero)
      (Bracket.square value))
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

cancelXSquare :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal._<_
    (Cross.q x)
    (BishopReal._*_
      (inverseSquare x (xNonzero inputs))
      (Bracket.square (Cross.gap (Cross.q x))))
cancelXSquare {x} inputs =
  let
    invX2 = inverseSquare x (xNonzero inputs)
    scaled =
      BishopP.*-monoʳ-<-pos
        (inverseSquarePositive
          (xNonzero inputs) (Unit.positive inputs))
        (Cross.negativeExpCrossReciprocalSquare inputs)
    leftCancel :
      BishopReal._≃_
        (BishopReal._*_
          invX2
          (BishopReal._*_ (Cross.q x) (Bracket.square x)))
        (Cross.q x)
    leftCancel =
      let open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 3
          (λ i q′ x′ →
            i ⊗ (q′ ⊗ (x′ ⊗ x′))
            ⊜ q′ ⊗ (i ⊗ (x′ ⊗ x′)))
          BishopP.≃-refl invX2 (Cross.q x) x)
        (BishopP.≃-trans
          (BishopP.*-congˡ
            (inverseSquareCancelsSquare x (xNonzero inputs)))
          (BishopP.*-identityʳ (Cross.q x)))
  in
  BishopP.<-respˡ-≃ leftCancel scaled

cancelGapSquare :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal._<_
    (BishopReal._*_
      (Cross.q x)
      (inverseSquare
        (Cross.gap (Cross.q x))
        (qGapNonzero inputs)))
    (inverseSquare x (xNonzero inputs))
cancelGapSquare {x} inputs =
  let
    gapQ = Cross.gap (Cross.q x)
    invGap2 = inverseSquare gapQ (qGapNonzero inputs)
    invX2 = inverseSquare x (xNonzero inputs)
    scaled =
      BishopP.*-monoʳ-<-pos
        (inverseSquarePositive
          (qGapNonzero inputs) (qGapPositive inputs))
        (cancelXSquare inputs)
    leftCommute :
      BishopReal._≃_
        (BishopReal._*_ invGap2 (Cross.q x))
        (BishopReal._*_ (Cross.q x) invGap2)
    leftCommute = BishopP.*-comm invGap2 (Cross.q x)
    rightCancel :
      BishopReal._≃_
        (BishopReal._*_
          invGap2
          (BishopReal._*_ invX2 (Bracket.square gapQ)))
        invX2
    rightCancel =
      let open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 3
          (λ g i v → g ⊗ (i ⊗ v)
            ⊜ i ⊗ (g ⊗ v))
          BishopP.≃-refl invGap2 invX2 (Bracket.square gapQ))
        (BishopP.≃-trans
          (BishopP.*-congˡ
            (inverseSquareCancelsSquare gapQ (qGapNonzero inputs)))
          (BishopP.*-identityʳ invX2))
  in
  BishopP.<-respʳ-≃ rightCancel
    (BishopP.<-respˡ-≃ leftCommute scaled)

negativeExpReciprocalSquareBound :
  ∀ {x} (inputs : Unit.PositiveUnitIntervalPoint x) →
  BishopReal._<_
    (BishopReal._*_
      (Cross.q x)
      (inverseSquare
        (Cross.gap (Cross.q x))
        (qGapNonzero inputs)))
    (inverseSquare x (xNonzero inputs))
negativeExpReciprocalSquareBound = cancelGapSquare

bishopNegativeExponentialReciprocalSquareDivisionLevel : ProofLevel
bishopNegativeExponentialReciprocalSquareDivisionLevel = machineChecked
