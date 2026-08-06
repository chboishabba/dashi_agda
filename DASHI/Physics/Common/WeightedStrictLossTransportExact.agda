module DASHI.Physics.Common.WeightedStrictLossTransportExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban III. Convergence",
-- Annales Henri Poincare 15 (2014), 2133--2175.
-- DOI: 10.1007/s00023-013-0303-3.
--
-- Peter Constantin and Ciprian Foias,
-- "Navier--Stokes Equations", University of Chicago Press, 1988.
-- DOI: 10.7208/chicago/9780226115498.001.0001.
--
-- DASHI CONTRIBUTION
--
-- Generalize the fixed one-half terminal-gap recursion to an arbitrary finite
-- sequence of rational transfer factors.  The same exact algebra can carry:
--
--   * RG gap pullback and Schur/remainder losses in Yang--Mills;
--   * retained dissipation minus interaction/tail losses in Navier--Stokes;
--   * typed hyperfabric transport with explicit residual cost.
--
-- No physical transfer factor or loss estimate is manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

record WeightedLossStep : Set where
  constructor weightedLossStep
  field
    transferFactor : ℚ
    stepLoss : ℚ

open WeightedLossStep public

pullBackFloor : ℚ → List WeightedLossStep → ℚ
pullBackFloor terminal [] = terminal
pullBackFloor terminal (step ∷ steps) =
  transferFactor step
  * (pullBackFloor terminal steps - stepLoss step)

terminalWeight : List WeightedLossStep → ℚ
terminalWeight [] = 1ℚ
terminalWeight (step ∷ steps) =
  transferFactor step * terminalWeight steps

discountedLoss : List WeightedLossStep → ℚ
discountedLoss [] = 0ℚ
discountedLoss (step ∷ steps) =
  transferFactor step
  * (discountedLoss steps + stepLoss step)

pullBackClosedForm :
  (terminal : ℚ) →
  (steps : List WeightedLossStep) →
  pullBackFloor terminal steps
  ≡ terminalWeight steps * terminal - discountedLoss steps
pullBackClosedForm terminal [] =
  ℚRing.solve-∀ terminal
pullBackClosedForm terminal (step ∷ steps)
  rewrite pullBackClosedForm terminal steps =
  ℚRing.solve-∀
    (transferFactor step)
    (terminalWeight steps)
    terminal
    (discountedLoss steps)
    (stepLoss step)

subtractRightMonotone :
  ∀ {left right} loss →
  left ≤ right →
  left - loss ≤ right - loss
subtractRightMonotone {left} {right} loss leftBelowRight =
  subst
    (λ lower → lower ≤ right - loss)
    (ℚRing.solve-∀ left loss)
    (subst
      (λ upper → left + (- loss) ≤ upper)
      (ℚRing.solve-∀ right loss)
      (ℚP.+-mono-≤ leftBelowRight ℚP.≤-refl))

marginBelowDifference :
  ∀ {margin budget total} →
  margin + budget ≤ total →
  margin ≤ total - budget
marginBelowDifference {margin} {budget} {total} admissible =
  let
    shifted :
      (margin + budget) - budget ≤ total - budget
    shifted = subtractRightMonotone budget admissible
  in
  subst
    (λ lower → lower ≤ total - budget)
    (ℚRing.solve-∀ margin budget)
    shifted

StrictMarginAdmissible :
  ℚ → ℚ → List WeightedLossStep → Set
StrictMarginAdmissible margin terminal steps =
  margin + discountedLoss steps
  ≤ terminalWeight steps * terminal

strictMarginBelowPullBack :
  ∀ margin terminal steps →
  StrictMarginAdmissible margin terminal steps →
  margin ≤ pullBackFloor terminal steps
strictMarginBelowPullBack margin terminal steps admissible =
  subst
    (λ selected → margin ≤ selected)
    (sym (pullBackClosedForm terminal steps))
    (marginBelowDifference admissible)

NonnegativeSurvivalAdmissible :
  ℚ → List WeightedLossStep → Set
NonnegativeSurvivalAdmissible terminal steps =
  discountedLoss steps ≤ terminalWeight steps * terminal

nonnegativeSurvivalIsZeroMargin :
  ∀ terminal steps →
  NonnegativeSurvivalAdmissible terminal steps
  ≡ StrictMarginAdmissible 0ℚ terminal steps
nonnegativeSurvivalIsZeroMargin terminal steps =
  cong
    (λ selected → selected ≤ terminalWeight steps * terminal)
    (ℚRing.solve-∀ (discountedLoss steps))

singleStepPullBackExact :
  ∀ terminal factor loss →
  pullBackFloor terminal
    (weightedLossStep factor loss ∷ [])
  ≡ factor * (terminal - loss)
singleStepPullBackExact terminal factor loss = refl

twoStepPullBackExact :
  ∀ terminal factor0 loss0 factor1 loss1 →
  pullBackFloor terminal
    ( weightedLossStep factor0 loss0
    ∷ weightedLossStep factor1 loss1
    ∷ [])
  ≡ factor0 * factor1 * terminal
    - (factor0 * loss0 + factor0 * factor1 * loss1)
twoStepPullBackExact terminal factor0 loss0 factor1 loss1 =
  ℚRing.solve-∀ terminal factor0 loss0 factor1 loss1
